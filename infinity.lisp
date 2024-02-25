(in-package :maxima)
(declare-top (special errorsw $radexpandr %pi-val expandflag exptrlsw rulesw timesp $ratinf))
;; ;some changes eg to timesin happened in Jan 2024. This was not updated..

;;; This file over-writes a bunch of programs from various
;;; files to implement 1/0 =oo, -1/0= -oo, 0/0 =indef, 0/-1 = -0,
;;; 0/1 would be +0 except we are just using the integer 0.

;;; see paper c:/papers/infinity.tex
(defun $rl()(load "d:/lisp/infinity.lisp")) ;  temporarily, easier to reload
(defvar $ratinf t) ;; if t or true, then allow 1/0 etc etc

;; the header for rat objects, share it
(defvar *ratsimpind '(rat simp)) ;should be (get 'rat 'msimpind) but isn't

;; special forms.
;; First, infinity oo  is 1/0
(defvar *ratinf `(,*ratsimpind 1 0))

;; negative infinity is -1/0
(defvar *ratminf `(,*ratsimpind -1 0))

;; indefinite is 0/0 but printed as indef
(defvar *ratind `(,*ratsimpind 0 0)) ;; indeterminate, unknown, ???

;; 1/(negative infinity)  is  minus 0, encoded as 0/-1,
;; the only rational number with a negative denominator.
(defvar *ratminuszero `(,*ratsimpind 0 -1))

;; test predicates,  just in case we change the representation:
;; user callable.
(defun $ratinf_p (x)(alike1 x *ratinf)) ;; test for oo
(defun $ratminf_p (x)(alike1 x *ratminf)) ;; test for -oo
(defun $ratind_p (x)(alike1 x *ratind)) ;; test for 0/0
(defun $ratminuszero_p (x)(alike1 x *ratminuszero)) ;; test for 0/-1
;; what about +0?  that's just the integer 0.

;; test for one of the extended numbers ... inf or indef or -0.
(defun $ratextended_p (x)
  (and (consp x)(eq (caar x) 'rat)
       (or
       (eq (caddr x) 0)  ;; a zero denominator means  oo or -00 or indef
       (eq (cadr x) 0))))  ;;alternatively 0/-1. Only way numerator is 0.

;; The remainder of this file is mostly
;; modified or re-written code from existing maxima source
;;
;; from simp.lisp

(defun zerop1 (x)
  (or (and (integerp x) (= 0 x))
      (and (floatp x) (= 0.0 x))
      (and ($bfloatp x) (= 0 (second x)))
      ($ratminuszero_p x) ;; changed 3/1/2022 RJF for -0 as ((rat) 0 -1)
      ))

(defmfun simpexpt (x y z);; rewritten gr-> Base, pot ->Power from simp.lisp..
  ;; the major framework of this program dates from 1963!
  (prog (Base Power check res rulesw w mlpBase mlpPower)
	;; save the input;
	;; if unchanged, return it to save memory/ share structure
	(setq check x)
	
	;; if  z=t, then the parts of x are already simplified
	(cond (z (setq Base (cadr x) Power (caddr x)) (go cont)))
	;; x must look like ((mexpt Base Power). 2 arguments only.
	(twoargcheck x)
	(setq Base (simplifya (cadr x) nil)) ;; the BASE
	(setq Power			     ;; the POWER
              (let (($%enumer $numer))
		;; Switch $%enumer on, when $numer is TRUE to allow 
		;; simplification of $%e to its numerical value.
		(simplifya (if $ratsimpexpons ($ratsimp (caddr x)) (caddr x))
                           nil)))
	;; This is the head of the main loop
	;; we come back here after making some small changes to
	;; continue processing
	
	cont

	;;
	(cond (($ratp Power) ;; is Power an mrat (CRE, canonical rational expr.)
               (setq Power (ratdisrep Power))
               (go cont))
	      
              (($ratp Base) ;; if Base canonical rational expression or taylor
               (cond ((member 'trunc (car Base) :test #'eq) ;truncated taylor series?
                      (return (srf (list '(mexpt) Base Power))))
		     
                     ((integerp Power)
                      (let ((varlist (caddar Base)) (genvar (cadddr (car Base))))
			(return (ratrep* (list '(mexpt) Base Power)))))
		     
                     (t ;not integer power, so disrep it, try again.
                      (setq Base (ratdisrep Base))
                      (go cont))))
	      
	      ;; maybe we have A^B where A or B
	      ;; is a matrix or list (i.e. vector)
              ((or (setq mlpBase (mxorlistp Base))
                   (setq mlpPower (mxorlistp Power)))
               (go matrix))
	      
              ((onep1 Power) (go atBase));; a^1
	      ;
              ((or (zerop1 Power) (onep1 Base))
	       ;;a^0 a^0.0 or a^0.0b0   OR  1^a or 1.0^a ... 
	       (go retno))
           
              ;; This next section of code tries to handle 0^a more completely
              ;; If a is explicit real and positive, 0^a is 0, 0.0, 0.0b0,
	      ;; If a is explicit real and negative, 0^a is indef.
	      ;; If a is explicit and complex, look at sign of realpart(a).
	      ;; If a is not known enough to find its sign,
	      ;; return an unchanged 0^a.
              ;; The handling of the flag *zexptsimp? is not changed.
	      ;;; uh, dunno about DK and old comment below RJF 3/8/22
	      ;; Reverting the return of an unsimplified 0^a, because timesin
              ;; can not handle such expressions. (DK 02/2010)

	      ;; Note that if we got here, power is not zero.
	   
              ((zerop1 Base)
;;;*****
	       ;; 0 to a non-zero power. [else we use previous clause]
	       ;; Base could be ((rat) 0 -1) i.e. -0. or just 0, 0.0, 0.0b0

               (cond ((or (member (setq z ($csign Power)) '($neg $nz)) ;Power<=0
			  (and *zexptsimp? (eq ($asksign Power) '$neg)))
		      ;; A negative exponent. Maxima error.?
                     (return (cond 
		       ($ratinf ;; are we using rat nums for oo, -oo,?
		     
			;; (format t "~%Power=~s Base=~s ratinf=~s ~%" Power Base $ratinf)
			(cond
				 (($ratminuszero_p Base) ; it is zero, but -0
				  ;; (-0)^(-1) to -1 power is minus inf..
				  (cond ((zerop1 Power) 1) ;;(-0)^0 is 1
					(($evenp Power) 0) ;e.g. (-0)^2 
					(($oddp Power) *ratminuszero) ; e.g.(-0)^3
					(t
					  (list (get 'mexpt 'msimpind) ;; don't know
					  ;;Base  is 0/-1
						(list '($signum) Power)))))
				 ;; zero but not -0
				 (t(list (get 'mexpt 'msimpind) ;; don't know
					  ;;Base  is 0
					 (list '($signum) Power)))))
		       

		       ;; $ratinf not t, return symbolic 0^a
				 ;;
				 ;;reminder.. Base is zero. 
				 ;; Power is NOT zero, also not a number
			(t (list (get 'mexpt 'msimpind) ;; don't know
				 Base
				 (list '($signum) Power)))))))
				 
;;; the rest of this, uh dunno..				 

		    ;; base is 0, just give error
			((not errorsw) (merror (intl:gettext "expt: undefined: 0 to a negative exponent.")))
			 
			(t (throw 'errorsw t))

	      ;; base is still zero.
		  
			((and (member z '($complex $imaginary))
			      ;; A complex exponent. Look at the sign of the realpart.
			      (member (setq z ($sign ($realpart Power))) 
				      '($neg $nz $zero)))
			 (cond ((not errorsw)
				(merror (intl:gettext "expt: undefined: 0 to a complex exponent.")))
			       (t (throw 'errorsw t))))
			
              ((and *zexptsimp? (eq ($asksign Power) '$zero))
               (cond ((not errorsw)
                      (merror (intl:gettext "expt: undefined: 0^0")))
                     (t (throw 'errorsw t))))
		  
              ((not (member z '($pos $pz)))
               ;; The sign of realpart(Power) is not known. We can not return
               ;; an unsimplified 0^a expression, because timesin can not
               ;; handle it. We return ZERO. That is the old behavior.
               ;; Look for the imaginary symbol to be consistent with 
               ;; old code.Huh/RJF
               (cond ((not (free Power '$%i))
                      (cond ((not errorsw)
                             (merror (intl:gettext "expt: undefined: 0 to a complex exponent.")))
                            
			    (t (throw 'errorsw t))))
                     (t
                      ;; Return ZERO and not an unsimplified expression.
                      (return (zerores Base Power)))
		     ))
              (t (return (zerores Base Power))))

	   ;;; BASE is NOT zero
           
           ((and (mnump Base)
                 (mnump Power)
                 (or (not (ratnump Base)) (not (ratnump Power))))
            (return (eqtest (exptrl Base Power) check)))
           ;; Check for numerical evaluation of the sqrt.
           ((and (alike1 Power '((rat) 1 2))
                 (or (setq res (flonum-eval '%sqrt Base))
                     (and (not (member 'simp (car x) :test #'eq))
                          (setq res (big-float-eval '%sqrt Base)))))
            (return res))
           ((eq Base '$%i)
            (return (%itopot Power)))
           ((and (realp Base) (minusp Base) (mevenp Power))
            (setq Base (- Base))
            (go cont))
           ((and (realp Base) (minusp Base) (moddp Power))
            (return (mul2 -1 (power (- Base) Power))))
           ((and (equal Base -1) (maxima-integerp Power) (mminusp Power))
            (setq Power (neg Power))
            (go cont))
           ((and (equal Base -1)
                 (maxima-integerp Power)
                 (mtimesp Power)
                 (= (length Power) 3)
                 (fixnump (cadr Power))
                 (oddp (cadr Power))
                 (maxima-integerp (caddr Power)))
            (setq Power (caddr Power))
            (go cont))
           ((atom Base) (go atBase))
           ((and (eq (caar Base) 'mabs)
                 (evnump Power)
                 (or (and (eq $domain '$real) (not (decl-complexp (cadr Base))))
                     (and (eq $domain '$complex) (decl-realp (cadr Base)))))
            (return (power (cadr Base) Power)))
           ((and (eq (caar Base) 'mabs)
                 (integerp Power)
                 (oddp Power)
                 (not (equal Power -1))
                 (or (and (eq $domain '$real) (not (decl-complexp (cadr Base))))
                     (and (eq $domain '$complex) (decl-realp (cadr Base)))))
            ;; abs(x)^(2*n+1) -> abs(x)*x^(2*n), n an integer number
            (if (plusp Power)
                (return (mul (power (cadr Base) (add Power -1))
                             Base))
                (return (mul (power (cadr Base) (add Power 1))
                             (inv Base)))))
           ((eq (caar Base) 'mequal)
            (return (eqtest (list (ncons (caar Base))
                                  (power (cadr Base) Power)
                                  (power (caddr Base) Power))
                            Base)))
           ((symbolp Power) (go opp))
           ((eq (caar Base) 'mexpt) (go e1))
           ((and (eq (caar Base) '%sum)
                 $sumexpand
                 (integerp Power)
                 (signp g Power)
                 (< Power $maxposex))
            (return (do ((i (1- Power) (1- i))
                         (an Base (simptimes (list '(mtimes) an Base) 1 t)))
                        ((signp e i) an))))
           ((equal Power -1) 
            (return (eqtest (testt (tms Base Power nil)) check)))
           ((fixnump Power)
            (return (eqtest (cond ((and (mplusp Base)
                                        (not (or (> Power $expop)
                                                 (> (- Power) $expon))))
                                   (expandexpt Base Power))
                                  (t (simplifya (tms Base Power nil) t)))
                            check))))
     
  opp
     (cond ((eq (caar Base) 'mexpt) (go e1))
           ((eq (caar Base) 'rat)
            (return (mul2 (power (cadr Base) Power)
                          (power (caddr Base) (mul2 -1 Power)))))
           ((not (eq (caar Base) 'mtimes)) (go up))
           ((or (eq $radexpand '$all) (and $radexpand (simplexpon Power)))
            (setq res (list 1))
            (go start))
           ((and (or (not (numberp (cadr Base)))
                     (equal (cadr Base) -1))
                 (equal -1 ($num Base)) ; only for -1
                 ;; Do not simplify for a complex base.
                 (not (member ($csign Base) '($complex $imaginary)))
                 (and (eq $domain '$real) $radexpand))
            ;; (-1/x)^a -> 1/(-x)^a for x negative
            ;; For all other cases (-1)^a/x^a
            (if (eq ($csign (setq w ($denom Base))) '$neg)
                (return (inv (power (neg w) Power)))
                (return (div (power -1 Power)
                             (power w Power)))))
           ((or (eq $domain '$complex) (not $radexpand)) (go up)))
     (return (do ((l (cdr Base) (cdr l)) (res (ncons 1)) (rad))
                 ((null l)
                  (cond ((equal res '(1))
                         (eqtest (list '(mexpt) Base Power) check))
                        ((null rad) 
                         (testt (cons '(mtimes simp) res)))
                        (t
                         (setq rad (power* ; RADEXPAND=()?
                                     (cons '(mtimes) (nreverse rad)) Power))
                         (cond ((not (onep1 rad))
                                (setq rad
                                      (testt (tms rad 1 (cons '(mtimes) res))))
                                (cond (rulesw
                                       (setq rulesw nil res (cdr rad))))))
                         (eqtest (testt (cons '(mtimes) res)) check))))
               ;; Check with $csign to be more complete. This prevents wrong 
               ;; simplifications like sqrt(-z^2)->%i*sqrt(z^2) for z complex.
               (setq z ($csign (car l)))
               (if (member z '($complex $imaginary))
                   (setq z '$pnz)) ; if appears complex, unknown sign
               (setq w (cond ((member z '($neg $nz) :test #'eq)
                              (setq rad (cons -1 rad))
                              (mult -1 (car l)))
                             (t (car l))))
               (cond ((onep1 w))
                     ((alike1 w Base) (return (list '(mexpt simp) Base Power)))
                     ((member z '($pn $pnz) :test #'eq)
                      (setq rad (cons w rad)))
                     (t
                      (setq w (testt (tms (simplifya (list '(mexpt) w Power) t)
                                          1 (cons '(mtimes) res))))))
               (cond (rulesw (setq rulesw nil res (cdr w))))))
     
  start
     (cond ((and (cdr res) (onep1 (car res)) (ratnump (cadr res)))
            (setq res (cdr res))))
     (cond ((null (setq Base (cdr Base)))
            (return (eqtest (testt (cons '(mtimes) res)) check)))
           ((mexptp (car Base))
            (setq y (list (caar Base) (cadar Base) (mult (caddar Base) Power))))
           ((eq (car Base) '$%i)
            (setq y (%itopot Power)))
           ((mnump (car Base))
            (setq y (list '(mexpt) (car Base) Power)))
           (t (setq y (list '(mexpt simp) (car Base) Power))))
     (setq w (testt (tms (simplifya y t) 1 (cons '(mtimes) res))))
     (cond (rulesw (setq rulesw nil res (cdr w))))
     (go start)
     
  retno  ;; might be 0^0
     (return (exptrl Base Power))
     
  atBase
     (cond ((zerop1 Power) (go retno)) ; 1^0 , 1.0^0.0 etc
           ((onep1 Power)
            (let ((y (mget Base '$numer)))
              (if (and y (floatp y) (or $numer (not (equal Power 1))))
                  ;; A numeric constant like %e, %pi, ... and 
                  ;; exponent is a float or bigfloat value.
                  (return (if (and (member Base *builtin-numeric-constants*)
                                   (equal Power bigfloatone))
                              ;; Return a bigfloat value.
                              ($bfloat Base)
                              ;; Return a float value.
                              y))
                  ;; In all other cases exptrl simplifies accordingly.
                  (return (exptrl Base Power)))))
           ((eq Base '$%e)
	    
	    (when (and $ratinf (ratnump Power)(= 0 (caddr Power))) ;; exp(0/0), 1/0, -1/0  RJF
	     (return (case (cadr Power) (0 *ratind)(-1 0)(1 *ratinf))))
            ;; Numerically evaluate if the power is a flonum.
            (when $%emode
              (let ((val (flonum-eval '%exp Power)))
                (when val
                  (return val)))
              ;; Numerically evaluate if the power is a (complex)
              ;; big-float.  (This is basically the guts of
              ;; big-float-eval, but we can't use big-float-eval.)
              (when (and (not (member 'simp (car x) :test #'eq))
                         (complex-number-p Power 'bigfloat-or-number-p))
                (let ((x ($realpart Power))
                      (y ($imagpart Power)))
                  (cond ((and ($bfloatp x) (like 0 y))
                         (return ($bfloat `((mexpt simp) $%e ,Power))))
                        ((or ($bfloatp x) ($bfloatp y))
                         (let ((z (add ($bfloat x) (mul '$%i ($bfloat y)))))
                           (setq z ($rectform `((mexpt simp) $%e ,z)))
                           (return ($bfloat z))))))))
            (cond ((and $logsimp (among '%log Power)) (return (%etolog Power)))
                  ((and $demoivre (setq z (demoivre Power))) (return z))
                  ((and $%emode
                        (among '$%i Power)
                        (among '$%pi Power)
                        ;; Exponent contains %i and %pi and %emode is TRUE:
                        ;; Check simplification of exp(%i*%pi*p/q*x)
                        (setq z (%especial Power)))
                   (return z))
                  (($taylorp (third x))
                   ;; taylorize %e^taylor(...)
                   (return ($taylor x)))))
           (t
            (let ((y (mget Base '$numer)))
              ;; Check for a numeric constant.
              (and y
                   (floatp y)
                   (or (floatp Power)
                       ;; The exponent is a bigfloat. Convert base to bigfloat.
                       (and ($bfloatp Power)
                            (member Base *builtin-numeric-constants*)
                            (setq y ($bfloat Base)))
                       (and $numer (integerp Power)))
                   (return (exptrl y Power))))))

  up 
     (return (eqtest (list '(mexpt) Base Power) check))

  matrix
     (cond ((zerop1 Power)
            (cond ((mxorlistp1 Base) (return (constmx (addk 1 Power) Base)))
                  (t (go retno))))
           ((onep1 Power) (return Base))
           ((or $doallmxops $doscmxops $domxexpt)
            (cond ((or (and mlpBase
                            (or (not ($listp Base)) $listarith)
                            (scalar-or-constant-p Power $assumescalar))
                       (and $domxexpt
                            mlpPower
                            (or (not ($listp Power)) $listarith)
                            (scalar-or-constant-p Base $assumescalar)))
                   (return (simplifya (outermap1 'mexpt Base Power) t)))
                  (t (go up))))
           ((and $domxmxops (member Power '(-1 -1.0) :test #'equal))
            (return (simplifya (outermap1 'mexpt Base Power) t)))
           (t (go up)))
  e1 
     ;; At this point we have an expression: (z^a)^b with Base = z^a and Power = b
     (cond ((or (eq $radexpand '$all)
                ;; b is an integer or an odd rational
                (simplexpon Power)
                (and (eq $domain '$complex)
                     (not (member ($csign (caddr Base)) '($complex $imaginary)))
                         ;; z >= 0 and a not a complex
                     (or (member ($csign (cadr Base)) '($pos $pz $zero))
                         ;; -1 < a <= 1
                         (and (mnump (caddr Base))
                              (eq ($sign (sub 1 (take '(mabs) (caddr Base))))
                                  '$pos))))
                (and (eq $domain '$real)
                     (member ($csign (cadr Base)) '($pos $pz $zero)))
                ;; (1/z)^a -> 1/z^a when z a constant complex
                (and (eql (caddr Base) -1)
                     (or (and $radexpand
                              (eq $domain '$real))
                         (and (eq ($csign (cadr Base)) '$complex)
                              ($constantp (cadr Base)))))
                ;; This does (1/z)^a -> 1/z^a. This is in general wrong.
                ;; We switch this type of simplification on, when
                ;; $ratsimpexpons is T. E.g. radcan sets this flag to T.
                ;; radcan hangs for expressions like sqrt(1/(1+x)) without
                ;; this simplification.
                (and $ratsimpexpons
                     (equal (caddr Base) -1))
                (and $radexpandr
                     (eq $domain '$real)
                     (odnump (caddr Base))))
            ;; Simplify (z^a)^b -> z^(a*b)
            (setq Power (mul Power (caddr Base))
                  Base (cadr Base)))
           ((and (eq $domain '$real)
                 (free Base '$%i)
                 $radexpand
                 (not (decl-complexp (cadr Base)))
                 (evnump (caddr Base)))
            ;; Simplify (x^a)^b -> abs(x)^(a*b)
            (setq Power (mul Power (caddr Base))
                  Base (radmabs (cadr Base))))
           ((and $radexpand
                 (eq $domain '$real)
                 (mminusp (caddr Base)))
            ;; Simplify (1/z^a)^b -> 1/(z^a)^b
            (setq Power (neg Power)
                  Base (power (cadr Base) (neg (caddr Base)))))
           (t (go up)))
    (go cont)))


(defun addk (x y)
  (cond ((eql x 0) y)
	((eql y 0) x)
	((and (numberp x) (numberp y))
         #+ignore (cl-or-bfloat-binary-op 'mplus '+ x y)
	 (+ x y)) ;just add them
	((or ($bfloatp x) ($bfloatp y)) ($bfloat (list '(mplus) x y)))
	(t (prog (g a b)
	      (cond ((numberp x)
		     (cond ((floatp x) (return (+ x (fpcofrat y))))
			   (t (setq x (list '(rat) x 1)))))
		    ((numberp y)
		     (cond ((floatp y) (return (+ y (fpcofrat x))))
			   (t (setq y (list '(rat) y 1))))))
	     (setq g (gcd (caddr x) (caddr y)))
	     
	     (cond ((= (caddr x) 0)
		    (cond((= (cadr x) 0)(return x))
			 ((= (caddr y) 0)
			  (return (if (equal x y) x ; oo+oo or -oo-oo
				    *ratind))))) ;oo-oo is und
		   ((= (caddr y) 0) ; return oo or -oo or und		   
		    (return y)))
	     
	    ;; above clause only change 12/2015 rjf
	     
	     (setq a (truncate (caddr x) g)
		   b (truncate (caddr y) g))

	     
	      (return (timeskl (list '(rat) 1 g)
			       (list '(rat)
				     (+ (* (cadr x) b)
					   (* (cadr y) a))
				     (* a b))))))))

(defun partition_ex_lisp   ;; hacked, simplified for this purpose
    (pred e)
  (let ((yes nil)(no nil))
    (map nil
	     #'(lambda(r) 
		 (if (funcall pred r)
                      (setf yes (cons r yes))
                                ; r fails predicate
                          (setf no (cons r no))))
               e)
           (cons yes no)))


(defun simptimes_ratinf (x)
  ;; here we combine floats, integers, ((rat) n d), bfloats, ((rat) n 0)
  ;; maybe common lisp  rats, complexes, intervals.
  ;; into one item. e.g.  ((mtimes) 0 ((rat) 1 0)  $r $s)
  ;; becomes ((mtimes)((rat) 0 0)  $r $s)
  ;; phew 
  ;;first pass, look for ANY  ((rat *) * 0)
  (if (notany #'$ratextended_p
	      (cdr x))
     x ;; no rational infinities or 0/0. quickest check, usually comes out here
    (let ((h (partition_ex_lisp  #'(lambda(r)(or (mnump r);; 1, 1.0, 1/2, 0/0, 1/0 also
						 (and (consp r)
						      (eq (caar r)'mrat))))
				 (cdr x))))
      ;; h is a list:  (yes . no ) ; yes is a list of pieces like 1/0, 0/0. no is rest
    (format t"~% h is ~s. ~%yes= ~s,~% no= ~s~%" h (car h)(cdr h) )
    (if (null(cdar h))
	#+ignore   (mul (caar h)($signum (cons '(mtimes) (cdr h))))
					; zero or only one item in yes part
					; just return same value

	;; above line breaks.
	x
      (infprod_hackit (car h)(cdr h))))))

;; nums is a list of 2 or more items.
;; look for at least one 0/0  --> 0.
;; look for at least one n/0 * 0 --> 0/0.
;;  (-1/0)^n  is  1/0 if n is even.  but  -3* (1/0) is -1/0 also.
;; need to check sign of all numbers.

(defun ratinfp(s)(and (consp s)
		   (eq (caar s) 'rat)
		   (equal (caddr s) 0)))

(defun infprod_hackit (nums rest) 
  (let ((poscount 0)(indefcount 0) (zerocount 0) (sign 0) (mrat nil))
    ;;counts of +oo -oo  0/0 0
    ;; mrat = t if the item encountered is mrat encoded not rat.
    ;; need to consider encoding -0, as one bonus.
    ;;sign
  (loop for s in nums do
	(cond((ratinfp s) ;denom is zero, look at numerator
	      (case (cadr s) ; numerator of ((rat) n d) is cadr
		(1 (incf poscount))
		(-1 (incf sign))
		(0 (incf indefcount))))
	     ;; the mrat case
	     ((and (consp s)
		   (eq (caar s) 'mrat)
		   (equal (cddr s) 0)) ;denom is zero, look at numerator
	      (setq mrat t)
	      (case (cadr s) ;; the numerator of ((mrat) . ( n . d))
		(1 (incf poscount))
		(-1 (incf sign))
		(0 (incf indefcount))))
	     
	     ;; not an infinity or indefinite
	     ((zerop1 s)		; 0 or 0.0 or 0.0b0
	      (incf zerocount))
	     ;leftover numbers, possibly bigfloat
	     ((and (mnump s)(mgrp 0 s)) (incf sign))))
  
;; (format t "~% pos=~s  indef=~s zer=~s sign=~s"	  poscount indefcount zerocount sign)
;;  here we make it an mrat if we encountered an mrat inf or 0/0
  (if mrat
     (list '(mtimes) (cons '(mrat simp nil nil) ; return mrat of oo -oo or 0/0
	    (cons
					; new numerator is..
	     (if (or (> indefcount 0)(> zerocount 0)) ;0/0 or 0* infinity
		 0 
	       (expt -1 sign))
					; (-1/0)^negcount
	     0)))

      (cons '(mtimes) ; return product: (rat of oo -oo or 0/0)* rest
	(cons
	 (cond ((or (> indefcount 0)(> zerocount 0)) ;0/0 or 0* infinity
		*ratind)
	       (t (list *ratsimpind (expt -1 sign) 0))) ; (-1/0)^negcount
	 rest)))))

  
(defmfun simptimes (x w z)			; W must be 1
  (prog (res check eqnflag matrixflag sumflag)
     (if (null (cdr x)) (return 1))
    (setq check x)
    
    (if $ratinf (setf x (simptimes_ratinf x)))
    
  start
    (setq x (cdr x))
    
    (cond ;;added 1/2016 .
    
     #+ignore
     ((and(consp  res) 
	;  (prog nil (format t "~%start res=~s x=~s" res x) t)
	  (member 0 (cdr res) :test #'(lambda(r s) ; car of res is (mtimes)
			   (and (consp s)
				(eq (caar s) 'rat)
				(= (caddr s) 0) ; denom is zero
				)))
	  (member 0 x))
     
    ;  (format t "~%DONE! res=~s x=~s" res x)
      (if (member 0 x) (return *ratind)  ;; 0*(1/0).  ;;; not there yet
	))
     
     
     
     ((zerop1 res) 
	   ;;; added 1/2016 RJF
      #+ignore
      (if (member 0 x :test #'(lambda(r s)
			   (and (consp s)
				(eq (caar s) 'rat)
				(= (caddr s) 0) ; denom is zero
				))) (return *ratind))

	    (cond ($mx0simp
		   (cond ((and matrixflag (mxorlistp1 matrixflag))
			  (return (constmx res matrixflag)))
			 (eqnflag (return (list '(mequal simp)
						(mul2 res (cadr eqnflag))
						(mul2 res (caddr eqnflag)))))
		         (t
		          (dolist (u x)
			    (cond ((mxorlistp u)
				   (return (setq res (constmx res u))))
				  ((and (mexptp u)
					(mxorlistp1 (cadr u))
					($numberp (caddr u)))
				   (return (setq res (constmx res (cadr u)))))
				  ((mequalp u)
				   (return
				     (setq res 
				           (list '(mequal simp)
						 (mul2 res (cadr u))
						 (mul2 res (caddr u))))))))))))
	    (return res))
	   ((null x) (go end)))
     (setq w (if z (car x) (simplifya (car x) nil)))
  st1
     (cond ((atom w) nil)
	   ((eq (caar w) 'mrat)
	    (cond ((or eqnflag matrixflag
	               (and sumflag
	                    (not (member 'trunc (cdar w) :test #'eq)))
		       (spsimpcases (cdr x) w))
	           (setq w (ratdisrep w))
	           (go st1))
	          (t
	           (return 
	             (ratf (cons '(mtimes)
			         (nconc (mapcar #'simplify (cons w (cdr x)))
					(cdr res))))))))
	   ((eq (caar w) 'mequal)
	    (setq eqnflag
		  (if (not eqnflag)
		      w
		      (list (car eqnflag)
			    (mul2 (cadr eqnflag) (cadr w))
			    (mul2 (caddr eqnflag) (caddr w)))))
	    (go start))
	   ((member (caar w) '(mlist $matrix) :test #'eq)
	    (setq matrixflag
		  (cond ((not matrixflag) w)
			((and (or $doallmxops $domxmxops $domxtimes)
			      (or (not (eq (caar w) 'mlist)) $listarith)
			      (not (eq *inv* '$detout)))
			 (stimex matrixflag w))
			(t (setq res (tms w 1 res)) matrixflag)))
	    (go start))
	   ((and (eq (caar w) '%sum) $sumexpand)
	    (setq sumflag (sumtimes sumflag w))
	    (go start)))
     (setq res (tms w 1 res))
     (go start)
  end
     (cond ((mtimesp res) (setq res (testt res))))
     (cond (sumflag (setq res (cond ((or (null res) (equal res 1)) sumflag)
				    ((not (mtimesp res))
				     (list '(mtimes) res sumflag))
				    (t (nconc res (list sumflag)))))))
     (cond ((or (atom res)
		(not (member (caar res) '(mexpt mtimes) :test #'eq))
		(and (zerop $expop) (zerop $expon))
		expandflag))
	   ((eq (caar res) 'mtimes) (setq res (expandtimes res)))
	   ((and (mplusp (cadr res))
		 (fixnump (caddr res))
		 (not (or (> (caddr res) $expop)
			  (> (- (caddr res)) $expon))))
	    (setq res (expandexpt (cadr res) (caddr res)))))
     (cond (matrixflag
            (setq res
                  (cond ((null res) matrixflag)
                        ((and (or ($listp matrixflag)
                                  $doallmxops
			          (and $doscmxops
			               (not (member res '(-1 -1.0) :test #'equal)))
			          ;; RES should only be -1 here (not = 1)
                                  (and $domxmxops
                                       (member res '(-1 -1.0) :test #'equal)))
                              (or (not ($listp matrixflag)) $listarith))
                         (mxtimesc res matrixflag))
			(t (testt (tms matrixflag 1 (tms res 1 nil))))))))
     (if res (setq res (eqtest res check)))
     (return (cond (eqnflag
		    (if (null res) (setq res 1))
		    (list (car eqnflag)
			  (mul2 (cadr eqnflag) res)
			  (mul2 (caddr eqnflag) res)))
		   (t res)))))


;; modifies product to include  factor^power

#+ignore
(defun tms (factor power product &aux tem)
  (prog ((rulesw nil)
	(z nil))
    (when (mplusp product) (setq product (list '(mtimes simp) product)))
    (cond ((zerop1 factor)  ;; 0^power
	   (cond ((mnegp power) ;; 0^negative_power)
		  (cond ($ratinf (return *ratind)) ;indefinite
			(t(if errorsw
			      (throw 'errorsw t)
			    (merror (intl:gettext "Division by 0"))))))
		 (t factor)))
	  
	  ((and $ratinf (alike1 factor *ratind))(return *ratind))
	  ((and $ratinf (alike1 factor *ratminf)) ;;(-oo)^power
	   (return(cond (($evenp power) *ratinf)
		 (($oddp power) *ratminf)
		 (t (list (get 'mexpt 'msimpind)
			  factor power))))
		;;;
		)
	  ((and $ratinf (alike1 factor *ratinf))  ;; oo^power
	   (return *ratinf))
	  ((and $ratinf (alike1 factor *ratminuszero))
	   (return
	    (cond ((zerop1 power) 1)   ;;(-0)^0 is 1
					 (($evenp power) 0)
					 (($oddp power) *ratminuszero)
					 (t (list (get 'mexpt 'msimpind)
						  factor power)))
	    )
	   )

	  
		 
	  ((and (null product)
		(or (and (mtimesp factor) (equal power 1))
		    (and (setq product (list '(mtimes) 1)) nil)))
	   (setq tem (append '((mtimes)) (if (mnump (cadr factor)) nil '(1))
			     (cdr factor) nil))
	   (if (= (length tem) 1)
	       (setq tem (copy-list tem))
	       tem))
	  ((mtimesp factor)
	   (do ((factor-list (cdr factor) (cdr factor-list)))
	       ((or (null factor-list) (zerop1 product))  product)
	     (setq z (timesin (car factor-list) (cdr product) power))
	     (when rulesw
	       (setq rulesw nil)
	       (setq product (tms-format-product z)))))
	  (t
	   (setq z (timesin factor (cdr product) power))
	   (if rulesw
	       (tms-format-product z)
	     product)))))

;;original tms
(defun tms (factor power product &aux tem)
  (let ((rulesw nil)
	(z nil))
    (when (mplusp product) (setq product (list '(mtimes simp) product)))
    (cond ((zerop1 factor)
	   (cond ((mnegp power)
		  (if errorsw
		      (throw 'errorsw t)
	      (merror (intl:gettext "Division by 0"))))
		 (t factor)))
	  ((and (null product)
		(or (and (mtimesp factor) (equal power 1))
		    (and (setq product (list '(mtimes) 1)) nil)))
	   (setq tem (append '((mtimes)) (if (mnump (cadr factor)) nil '(1))
			     (cdr factor) nil))
	   (if (= (length tem) 1)
	       (setq tem (copy-list tem))
	       tem))
	  ((mtimesp factor)
	   (do ((factor-list (cdr factor) (cdr factor-list)))
	       ((or (null factor-list) (zerop1 product))  product)
	     (setq z (timesin (car factor-list) (cdr product) power))
	     (when rulesw
	       (setq rulesw nil)
	       (setq product (tms-format-product z)))))
	  (t
	   (setq z (timesin factor (cdr product) power))
	   (if rulesw
	       (tms-format-product z)
	       product)))))


;; we do   need this change.??
(defun *red (n d)
  (cond ((zerop n)(if $ratinf (list *ratsimpind
				    0 (if (numberp d)(cond ((< d 0) -1)((= d 0) 0)(t 1))
				    0)) 0))	; 0/x is 0. 0/-5 is -0 1/2015 rjf
	((equal d 1) n)
	((equal d 0) (list *ratsimpind (signum n) d)) ;; changed 12/2015 rjf
	(t (let ((u (gcd n d)))
	     (setq n (truncate n u)
	           d (truncate d u))
	     (if (minusp d) (setq n (- n) d (- d)))
	     (cond ((equal d 1) n)
		   ($float (fpcofrat1 n d))
		   (t (list *ratsimpind n d)))))))

(defun simpmin (x vestigial z)
  (declare (ignore vestigial))
  (cond ((null (cdr x)) 0)
	((equal 0 (cadr x)) `(,*ratsimpind 0 -1))  ;rjf 1/2016  -0
        ((null (cddr x))
	 (mul -1 (simplifya (cadr x) z)))
        (t
         ;; ((mminus) a b ...) -> ((mplus) a ((mtimes) -1 b) ...)
         (sub (simplifya (cadr x) z) (addn (cddr x) z)))))

(defmfun simpquot (x y z)
  (twoargcheck x)
  (cond ((and (integerp (cadr x)) (integerp (caddr x)) (not (zerop (caddr x))))
	 (*red (cadr x) (caddr x)))
	((and (numberp (cadr x)) (numberp (caddr x)) (not (zerop (caddr x))))
	 (/ (cadr x)(caddr x))
         #+ignore (cl-or-bfloat-binary-op 'mquotient '/ (cadr x) (caddr x))
	 )
	(t (setq y (simplifya (cadr x) z))
	   (setq x (simplifya (list '(mexpt) (caddr x) -1) z))
	   (if (equal y 1) x (simplifya (list '(mtimes) y x) t)))))


(defmfun exptrl (r1 r2)  ;compute r1^r2, both numbers of some sort
  (cond ((equal r2 1) r1)
        ((equal r2 1.0) 
         (cond ((mnump r1) (addk 0.0 r1))
               ;; Do not simplify the type of the number away.
               (t (list '(mexpt simp) r1 1.0))))
        ((equal r2 bigfloatone)
         (cond ((mnump r1) ($bfloat r1))
               ;; Do not simplify the type of the number away.
               (t (list '(mexpt simp) r1 bigfloatone))))
	((zerop1 r1)
	 
	 (cond 
	  ;; changed 1/2016 RJF
	  ((or (zerop1 r2) (mnegp r2))
	   (cond #+ignore($ratinf *ratind) ;; this is RJF possible change.
		 		 ;; for instance, mathematica says Indeterminate.
		 ($ratinf 1) ;; or this? Knuth says 1 2/22/22
		 ((not errorsw)
		    (merror (intl:gettext "expt: undefined: ~M") (list '(mexpt) r1 r2)))
		 (t (throw 'errorsw t))))
	  (t (zerores r1 r2))))
	((alike1 r2 *ratinf) (mul (signum r1) *ratinf)) ;new rjf
	((alike1 r2 *ratind) *ratind)	;new rjf
	((alike1 r1 *ratind) *ratind)	;new rjf

	((or (zerop1 r2) (onep1 r1))
	 (cond ((or ($bfloatp r1) ($bfloatp r2)) bigfloatone)
	       ((or (floatp r1) (floatp r2)) 1.0)
	       (t 1)))
	((or ($bfloatp r1) ($bfloatp r2)) ($bfloat (list '(mexpt) r1 r2)))
	((and (numberp r1) (integerp r2)) (exptb r1 r2))
	((and (numberp r1) (floatp r2) (equal r2 (float (floor r2))))
	 (exptb (float r1) (floor r2)))
	((or $numer (and (floatp r2) (or (plusp (num1 r1)) $numer_pbranch)))
	 (let (y  #+kcl(r1 r1) #+kcl(r2 r2))
	   (cond ((mnegp (setq r1 (addk 0.0 r1)))
		  (cond ((or $numer_pbranch (eq $domain '$complex))
		         ;; for R1<0:
		         ;; R1^R2 = (-R1)^R2*cos(pi*R2) + i*(-R1)^R2*sin(pi*R2)
			 (setq r2 (addk 0.0 r2))
			 (setq y (exptrl (- r1) r2) r2 (* %pi-val r2))
			 (add2 (* y (cos r2))
			       (list '(mtimes simp) (* y (sin r2)) '$%i)))
			(t (setq y (let ($numer $float $keepfloat $ratprint)
				     (power -1 r2)))
			   (mul2 y (exptrl (- r1) r2)))))
	         ((equal (setq r2 (addk 0.0 r2)) (float (floor r2)))
	          (exptb r1 (floor r2)))
	         ((and (equal (setq y (* 2.0 r2)) (float (floor y)))
	               (not (equal r1 %e-val)))
		  (exptb (sqrt r1) (floor y)))
                 ;; If bfloat conversion turned r1 or r2 into a bigfloat, we
                 ;; can't call cl:exp or cl:log here, but we *can* safely
                 ;; recurse (which will usually give a noun form that then gets
                 ;; simplified)
                 ((or ($bfloatp r1) ($bfloatp r2))
                  (exptrl r1 r2))
		 (t
                  (exp (* r2 (log r1)))))))
	((floatp r2) (list '(mexpt simp) r1 r2))
	((integerp r2) ;; here we are left with rat^power RJF
	 (cond ((minusp r2)
		;; this looks dubious too RJF. 1/2016. I'd like (-1/0)^-1
		;; to come out as -0. and (-0)^-1 to be (-1/0).i.e. -oo.
		;; some lisps may have (* -1 0) be -0. which would be right.
		;; but may never happen in others. most others. RJF
		(if

		    (and $ratinf 
		      (= 0 (caddr r1))) ;; (n/0) ^ -1
			 #+ignore
		  '((rat) 0 0)		;rjf
		 ;; (list '(rat)0 (cadr r1) )  ; 0/n is 0, unless n is -1?
		  (if (< (cadr r1) 0 ) (list *ratsimpind 0 -1) 0)
		
	        (exptrl (cond ((equal (abs (cadr r1)) 1)
	                       (* (cadr r1) (caddr r1)))
	                       ;; We set the simp flag at this place. This
	                       ;; changes nothing for an exponent r2 # -1.
	                       ;; exptrl is called again and does not look at
	                       ;; the simp flag. For the case r2 = -1 exptrl
	                       ;; is called with an exponent 1. For this case
	                       ;; the base is immediately returned. Now the
	                       ;; base has the correct simp flag. (DK 02/2010)
			      ((minusp (cadr r1))
			       (list *ratsimpind (- (caddr r1)) (- (cadr r1))))
			      (t (list *ratsimpind (caddr r1) (cadr r1))))
			(- r2))))
	       (t (list *ratsimpind (exptb (cadr r1) r2) (exptb (caddr r1) r2)))))

	((and (floatp r1) (alike1 r2 '((rat) 1 2)))
	 ;; this all looks dubious-- RJF.  There are 2 square roots. 1/2016
	 (if (minusp r1)
	     (list '(mtimes simp) (sqrt (- r1)) '$%i)
	     (sqrt r1)))
	((and (floatp r1) (alike1 r2 '((rat) -1 2)))
	 (if (minusp r1)
	     (list '(mtimes simp) (/ -1.0 (sqrt (- r1))) '$%i)
	     (/ (sqrt r1))))
	((floatp r1)
	 (if (plusp r1)
	     (exptrl r1 (fpcofrat r2))
	     (mul2 (exptrl -1 r2) ;; (-4.5)^(1/4) -> (4.5)^(1/4) * (-1)^(1/4)
		   (exptrl (- r1) r2))))
	(exptrlsw (list '(mexpt simp) r1 r2))
	(t
	 (let ((exptrlsw t))
	   (simptimes (list '(mtimes)
			    (exptrl r1 (truncate (cadr r2) (caddr r2)))
			    (let ((y (let ($keepfloat $ratprint)
				       (simpnrt r1 (caddr r2))))
				  (z (rem (cadr r2) (caddr r2))))
			      (if (mexptp y)
				  (list (car y) (cadr y) (mul2 (caddr y) z))
				  (power y z))))
		      1 t)))))















;;from nforma.lisp

#+ignore
(setf (get 'rat 'formatter) 
  #'(lambda(form)(cond ((minusp (cadr form))
			(list '(mminus) (list '(rat) (- (cadr form)) (caddr form))))
		       (t (cons '(rat) (cdr form))))))
(setf (get 'rat 'formatter) 
  #'(lambda(form)(cond 

		       
		       ;; next clauses 1/2016, Rjf
		       ((and (= 0 (cadr form))(= -1 (caddr form))) ;-0
			(list '(mminus) 0))
		       ((= 0 (caddr form)) ; inf? indef?
			(case (cadr form)
			  (1 '$oo)
			  (-1 '$\-oo)
			  (0 '$indef)))
		       ((minusp (cadr form)) ;neg numerator
			(list '(mminus) (list '(rat) (- (cadr form)) (caddr form))))
			
		       (t (cons '(rat) (cdr form))))))




;;; from trigi.lisp
;;; example of how to do ratinf
(defmfun simp-%sin (form y z) 
  (oneargcheck form)
  (setq y (simpcheck (cadr form) z))
  (cond ((flonum-eval (mop form) y))
	((and (not (member 'simp (car form))) (big-float-eval (mop form) y)))
	((taylorize (mop form) (second form)))
	((and $%piargs (cond ((zerop1 y) 0)
			     ((has-const-or-int-term y '$%pi) (%piargs-sin/cos y)))))
	((and $%iargs (multiplep y '$%i)) (mul '$%i (cons-exp '%sinh (coeff y '$%i 1))))
	((and $triginverses (not (atom y))
	      (cond ((eq '%asin (setq z (caar y))) (cadr y))
		    ((eq '%acos z) (sqrt1-x^2 (cadr y)))
		    ((eq '%atan z) (div (cadr y) (sqrt1+x^2 (cadr y))))
		    ((eq '%acot z) (div 1 (sqrt1+x^2 (cadr y))))
		    ((eq '%asec z) (div (sqrtx^2-1 (cadr y)) (cadr y)))
		    ((eq '%acsc z) (div 1 (cadr y)))
		    ((eq '$atan2 z) (div (cadr y) (sq-sumsq (cadr y) (caddr y)))))))
	((and $trigexpand (trigexpand '%sin y)))
	($exponentialize (exponentialize '%sin y))
	((and $halfangles (halfangle '%sin y)))
	((apply-reflection-simp (mop form) y $trigsign))
					;((and $trigsign (mminusp* y)) (neg (cons-exp '%sin (neg y))))
	((and $ratinf (ratnump y)(= 0 (caddr y)))  ;; added for 0/0 etc  RJF 1/2016
	 (list *ratsimpind 0 0))		; denominator is zero. numerator 0,1,-1 -- all same value of sin()

	(t (eqtest (list '(%sin) y) form))))


;;; from compar.lisp

(defmfun infsimp* (e) ;; redone entirely RJF 1/2016
  
  (cond
       ((and $ratinf (ratnump e)(= (caddr e) 0)) (cadr e)
	;(case (cadr e)(0 '$und)(1 '$pos)(-1 '$neg))
	)
       ((or (atom e) (and (free e '$inf) (free e '$minf)))
	e)
    (t (infsimp e))))

;;  There is no function $signum.  It is all done here.
(defmfun simpsignum (e y z)
  (declare (ignore y))
  (oneargcheck e)
  (if(and $ratinf (ratnump (cadr e))
		(= 0 (caddr (cadr e)))) ;; rjf sign of n/0.  
	   ;;sign of 0/0 is ??
	   (if (= 0 (cadr (cadr e))) e
	     (cadr (cadr e)))
    (let ((x (simpcheck (second e) z)) ;x is the argument of signum
	  (sgn nil))
    (cond 

	  ((complex-number-p x #'mnump)
		    (if (complex-number-p x #'$ratnump) ;; nonfloat complex
		        (if (zerop1 x) 0 ($rectform (div x ($cabs x))))
		      (maxima::to (bigfloat::signum (bigfloat::to x)))))
		   
	  ;; idemPotent: signum(signum(z)) = signum(z).
	  ((and (consp x) (consp (car x)) (eq '%signum (mop x))) x)
		   
	  (t
	   (setq sgn ($csign x))
	   
	   (cond ((eq sgn '$neg) -1)
		 ((eq sgn '$zero) 0)
		 ((eq sgn '$pos) 1)

		 ;; multiplicative: signum(ab) = signum(a) * signum(b).
		 ((mtimesp x)
		  (muln (mapcar #'(lambda (s) (take '(%signum) s)) (margs x)) t))

		 ;; Reflection rule: signum(-x) --> -signum(x).
		 ((great (neg x) x) (neg (take '(%signum) (neg x))))
	
		 ;; nounform return
		 (t (eqtest (list '(%signum) x) e))))

	  ))))

;; new version doesn't work
#+ignore (defmfun simpsignum (e y z)
  (declare (ignore y))
  (oneargcheck e)
  (if(and $ratinf (ratnump (cadr e))
		(= 0 (caddr (cadr e)))) ;; rjf sign of n/0.  
	   ;;sign of 0/0 is ??
	   (if (= 0 (cadr (cadr e))) e
	     (cadr (cadr e)))

    ;;else
    ($signum e)))
    

;;; the following section is an attempt to
;;; over-wrap the $limit and $integrate programs to
;;; use these conventions.
;;; It would be nice if solve(1/x=inf,x) got x=0,
;;; but it doesn't so there is not much point in wrapping it.

;; fixing up limit,hackish.

(defvar limit-redefined nil)		; do this only once
(defvar integrate-redefined nil)	; do this only once

(unless limit-redefined 
  (setf (symbol-function '$old-limit)
    (symbol-function '$limit))
  (setf limit-redefined t))

(unless integrate-redefined  ;; nicer would be to store old def on proplist?
  (setf (symbol-function '$old-integrate)
    (symbol-function '$integrate))
  (setf (symbol-function 'old-simpinteg)
      (symbol-function 'simpinteg))
  (setf integrate-redefined t))

(defun $limit(&rest z)
  (let ((oldans (apply '$old-limit z))
	(newans nil))
;;    (format t "~%old-limit returns ~s" oldans)
    (setf newans
      (sublis
     '(
       ($inf . *ratinf)		;should cover minf too
       ($und . *ratind)
       ($infinity . *ratind)	; "complex infinity"?
       ($ind . *ratind)) ; bounded but unknown?? maybe interval(-oo,oo)
     oldans))
;;    (format t "~%newans is ~s" newans)
    (simplifya     newans     nil)))

(defun $integrate(&rest z)
  (let ((oldans (apply '$old-integrate z))
	(newans nil))
    (setf newans
	  (sublis
	   '(
	     ($inf . *ratinf)	;should cover minf too
	     ($und . *ratind)
	     ($infinity . *ratind)	; "complex infinity"?
	     ($ind . *ratind)) ; bounded but unknown?? maybe interval(-oo,oo)
	   oldans))
    ;;  (format t "~%newans is ~s" newans)
    (simplifya     newans     nil)))

(defun simpinteg(&rest z)
  (let ((oldans (apply 'old-simpinteg z))
	(newans nil))
    (setf newans
	  (sublis
	   '(
	     ($inf . *ratinf)	;should cover minf too
	     ($und . *ratind)
	     ($infinity . *ratind)	; "complex infinity"?
	     ($ind . *ratind)) ; bounded but unknown?? maybe interval(-oo,oo)
	   oldans))
    (simplifya     newans     nil)))

	      
;; from simp.lisp

(defun addk (x y)
  (cond ((eql x 0) y)
	((eql y 0) x)
	((and (numberp x) (numberp y))
         #+ignore (cl-or-bfloat-binary-op 'mplus '+ x y)
	 (+ x y))
	;; new, for infinities
	((ratinfp x) (if (alike1 x y) x (if (ratinfp y) *ratind x )))
	((ratinfp y) y)
	((or ($bfloatp x) ($bfloatp y)) ($bfloat (list '(mplus) x y)))
	
	(t (prog (g a b)
	      (cond ((numberp x)
		     (cond ((floatp x) (return (+ x (fpcofrat y))))
			   (t (setq x (list *ratsimpind x 1)))))
		    ((numberp y)
		     (cond ((floatp y) (return (+ y (fpcofrat x))))
			   (t (setq y (list *ratsimpind y 1))))))
	      (setq g (gcd (caddr x) (caddr y)))
	      (setq a (truncate (caddr x) g)
	            b (truncate (caddr y) g))
	      (return (timeskl (list *ratsimpind 1 g)
			       (list *ratsimpind
				     (+ (* (cadr x) b)
					   (* (cadr y) a))
				     (* a b))))))))









;;; rat (x/0) requires fix  to ratreduce and ratinvert from rat3b.lisp

(defmfun ratreduce (x y &aux b)
  (cond					;((pzerop y) (rat-error "quotient by zero"))
   ((pzerop y) 
    (if (pzerop x) '( 0 . 0) '(1 . 0))) ;; change! rjf 2/2016
   ((pzerop x) (rzero))
	((equal y 1) (cons x 1))
	((and $keepfloat (pcoefp y) (or $float (floatp y) (pfloatp x)))
	 (cons (pctimes (quotient 1.0 y) x) 1))
	(t (setq b (pgcdcofacts x y))
	   (setq b (ratalgdenom (rplacd (cdr b) (caddr b))))
	   (cond ((and modulus (pcoefp (cdr b)))
		  (cons (pctimes (crecip (cdr b)) (car b)) 1))
		 ((pminusp (cdr b))
		  (cons (pminus (car b)) (pminus (cdr b))))
		 (t b)))))


(defun ratinvert (y)
  (ratalgdenom
   (cond ;;((pzerop (car y)) (rat-error "`quotient' by `zero'"))
    ((pzerop (car y)) '(1 . 0)) ;; changed 2/2016 RJF
	 ((and modulus (pcoefp (car y)))
	  (cons (pctimes (crecip (car y)) (cdr y)) 1))
	 ((and $keepfloat (floatp (car y)))
	  (cons (pctimes (/ (car y)) (cdr y)) 1))
	 ((pminusp (car y)) (cons (pminus (cdr y)) (pminus (car y))))
	 (t (cons (cdr y) (car y))))))

#+ignore
(defmfun rattimes (x y gcdsw) ; no change,, yet
  (cond ($ratfac (facrtimes x y gcdsw))
	((and $algebraic gcdsw (ralgp x) (ralgp y))
	 (let ((w  (rattimes x y nil)))
	   (ratreduce (car w) (cdr w))))
	((equal 1 (cdr x))
	 (cond ((equal 1 (cdr y)) (cons (ptimes* (car x) (car y)) 1))
	       (t (cond (gcdsw (rattimes (ratreduce (car x) (cdr y))
					 (cons (car y) 1) nil))
			(t (cons (ptimes* (car x) (car y)) (cdr y)))))))
	((equal 1 (cdr y)) (rattimes y x gcdsw))
	(t (cond (gcdsw (rattimes (ratreduce (car x) (cdr y))
				  (ratreduce (car y) (cdr x)) nil))
		 (t (cons (ptimes* (car x) (car y))
			  (ptimes* (cdr x) (cdr y))))))))

;; must fix ratdisprep or nformat so  ((mrat ..) 0 . 0)
;; prints better .. not as 0  !!

;; from rat3e

(defun cdisrep (x &aux n d sign)
  (cond 
   ((pzerop (cdr x)) (if (pzerop (car x)) *ratind *ratinf))
   ((pzerop (car x)) 0)
	((or (equal 1 (cdr x)) (floatp (cdr x))) (pdisrep (car x)))
	(t (setq sign (cond ($ratexpand (setq n (pdisrep (car x))) 1)
			    ((pminusp (car x))
			     (setq n (pdisrep (pminus (car x)))) -1)
			    (t (setq n (pdisrep (car x))) 1)))
	   (setq d (pdisrep (cdr x)))
	   (cond ((and (numberp n) (numberp d))
		  (list *ratsimpind (* sign n) d))
		 ((and $ratdenomdivide $ratexpand
		       (not (atom n))
		       (eq (caar n) 'mplus))
		  (fancydis n d))
		 ((numberp d)
		  (list '(mtimes ratsimp)
			(list *ratsimpind sign d) n))
		 ((equal sign -1)
		  (cons '(mtimes ratsimp)
			(cond ((numberp n)
			       (list (* n -1)
				     (list '(mexpt ratsimp) d -1)))
			      (t (list sign n (list '(mexpt ratsimp) d -1))))))
		 ((equal n 1)
		  (list '(mexpt ratsimp) d -1))
		 (t (list '(mtimes ratsimp) n
			  (list '(mexpt ratsimp) d -1)))))))


;; there are lots of comments in the original file simp.lisp regarding
;; adding..

(defun addk (x y)
  (cond ((eql x 0)(if (alike1 y *ratminuszero) 0 y)) ;; 0+ (-0) is 0 rjf 2/26/22
	((eql y 0)(if (alike1 x *ratminuszero) 0 x))
	((and (numberp x) (numberp y)) (+ x y))
	((or ($bfloatp x) ($bfloatp y)) ($bfloat (list '(mplus) x y)))
	(t (prog (g a b)
	      (cond ((numberp x)
		     (cond ((floatp x) (return (+ x (fpcofrat y))))
			   (t (setq x (list '(rat) x 1)))))
		    ((numberp y)
		     (cond ((floatp y) (return (+ y (fpcofrat x))))
			   (t (setq y (list '(rat) y 1))))))
	      (setq g (gcd (caddr x) (caddr y)))
	      (setq a (truncate (caddr x) g)
	            b (truncate (caddr y) g))
	      (return (timeskl (list '(rat) 1 g)
			       (list '(rat)
				     (+ (* (cadr x) b)
					   (* (cadr y) a))
				     (* a b))))))))

(defun pls (x out)
  (prog (fm *plusflag*)
     (if (mtimesp x) (setq x (testtneg x)))
     (when (and $numer (atom x) (eq x '$%e))
       ;; Replace $%e with its numerical value, when $numer ist TRUE
       (setq x %e-val))
     
     (cond ((alike1 x *ratind) (return x)) ;; 2/26/22 RJF check for 0/0
	   ((null out)
            ;; Initialize a form like ((mplus) <number> expr)
            (return
              (cons '(mplus)
                    (cond ((mnump x) (ncons x))
                          ((not (mplusp x))
                           (list 0 (cond ((atom x) x) (t (copy-list x)))))
                          ((mnump (cadr x)) (copy-list (cdr x) ))
                          (t (cons 0 (copy-list (cdr x) )))))))
           ((mnump x)
            ;; Add a number into the first term of the list out.
            (return (cons '(mplus)
                          (if (mnump (cadr out))
                              (cons (addk (cadr out) x) (cddr out))
                              (cons x (cdr out))))))
           ((not (mplusp x)) (plusin x (cdr out)) (go end)))
     ;; At this point we have a mplus expression as argument x. The following
     ;; code assumes that the argument x is already simplified and the terms
     ;; are in a canonical order.
     ;; First we add the number to the first term of the list out.
     (rplaca (cdr out)
             (addk (if (mnump (cadr out)) (cadr out) 0)
                   (cond ((mnump (cadr x)) (setq x (cdr x)) (car x)) (t 0))))
     ;; Initialize fm with the list of terms and start the loop to add the
     ;; terms of an mplus expression into the list out.
     (setq fm (cdr out))
  start
     (if (null (setq x (cdr x))) (go end))
     ;; The return value of PLUSIN is a list, where the first element is the
     ;; added argument and the rest are the terms which follow the added
     ;; argument.
     (setq fm (plusin (car x) fm))
     (go start)
  end
     (if (not *plusflag*) (return out))
     (setq *plusflag* nil)   ; *PLUSFLAG* T handles e.g. a+b+3*(a+b)-2*(a+b)
  a  
     ;; *PLUSFLAG* is set by PLUSIN to indicate that a mplus expression is
     ;; part of the result. For this case go again through the terms of the
     ;; result and add any term of the mplus expression into the list out.
     (setq fm (cdr out))
  loop
     (when (mplusp (cadr fm))
       (setq x (cadr fm))
       (rplacd fm (cddr fm))
       (pls x out)
       (go a))
     (setq fm (cdr fm))
     (if (null (cdr fm)) (return out))
     (go loop)))
;;#+ignore ;;; original
(defun timesin (x y w)                  ; Multiply X^W into Y
  (prog (fm temp z check u expo)
     (if (mexptp x) (setq check x))
  top
     ;; Prepare the factor x^w and initialize the work of timesin
     (cond ((equal w 1)
            (setq temp x))
           (t
            (setq temp (cons '(mexpt) (if check 
                                          (list (cadr x) (mult (caddr x) w))
                                          (list x w))))
            (if (and (not timesinp) (not (eq x '$%i)))
                (let ((timesinp t))
                  (setq temp (simplifya temp t))))))
     (setq x (if (mexptp temp)
                 (cdr temp)
                 (list temp 1)))
     (setq w (cadr x)
           fm y)
  start
     ;; Go through the list of terms in fm and look what is to do.
     (cond ((null (cdr fm))
            ;; The list of terms is empty. The loop is finshed.
            (go less))
           ((or (and (mnump temp)
                     (not (or (integerp temp)
                              (ratnump temp))))
                (and (integerp temp)
                     (equal temp -1)))
            ;; Stop the loop for a float or bigfloat number, or number -1.
            (go less))
           ((mexptp (cadr fm))
            (cond ((alike1 (car x) (cadadr fm))
                   (cond ((zerop1 (setq w (plsk (caddr (cadr fm)) w)))
                          (go del))
                         ((and (mnump w)
                               (or (mnump (car x))
                                   (eq (car x) '$%i)))
                          (rplacd fm (cddr fm))
                          (cond ((mnump (setq x (if (mnump (car x))
                                                    (exptrl (car x) w)
                                                    (power (car x) w))))
                                 (return (rplaca y (timesk (car y) x))))
                                ((mtimesp x)
                                 (go times))
                                (t
                                 (setq temp x
                                       x (if (mexptp x) (cdr x) (list x 1)))
                                 (setq w (cadr x)
                                       fm y)
                                 (go start))))
                         ((maxima-constantp (car x))
                          (go const))
                         ((onep1 w)
                          (cond ((mtimesp (car x))
                                 ;; A base which is a mtimes expression. Remove
                                 ;; the factor from the lists of products.
                                 (rplacd fm (cddr fm))
                                 ;; Multiply the factors of the base with
                                 ;; the list of all remaining products.
                                 (setq rulesw t)
                                 (return (muln (nconc y (cdar x)) t)))
                                (t (return (rplaca (cdr fm) (car x))))))
                         (t
                          (go spcheck))))
                  ;; At this place we have to add code for a rational number
                  ;; as a factor to the list of products.
                  ((and (onep1 w)
                        (or (ratnump (car x))
                            (and (integerp (car x))
                                 (not (onep (car x))))))
                   ;; Multiplying bas^k * num/den
                   (let ((num (num1 (car x)))
                         (den (denom1 (car x)))
                         (bas (second (cadr fm))))
                     (cond ((and (integerp bas)
                                 (not (eql 1 (abs bas)))
                                 (setq expo (exponent-of (abs num) bas)))
                            ;; We have bas^m*bas^k = bas^(k+m).
                            (setq temp (power bas
                                              (add (third (cadr fm)) expo)))
                            ;; Set fm to have 1/denom term.
                            (setq x (mul (car y)
                                         (div (div num
                                                   (exptrl bas expo))
                                              den))))
                           ((and (integerp bas)
                                 (not (eql 1 (abs bas)))
                                 (setq expo (exponent-of den bas)))
                            (setq expo (- expo))
                            ;; We have bas^(-m)*bas^k = bas^(k-m).
                            (setq temp (power bas
                                              (add (third (cadr fm)) expo)))
                            ;; Set fm to have the numerator term.
                            (setq x (mul (car y)
                                         (div num
                                              (div den
                                                   (exptrl bas (- expo)))))))
                           (t
                            ;; Next term in list of products.
                            (setq fm (cdr fm))
                            (go start)))
                     ;; Add in the bas^(k+m) term or bas^(k-m)
                     (setf y (rplaca y 1))
                     (rplacd fm (cddr fm))
                     (rplacd fm (cons temp (cdr fm)))
                     (setq temp x
                           x (list x 1)
                           w 1
                           fm y)
                     (go start)))
                  ((and (not (atom (car x)))
                        (eq (caar (car x)) 'mabs)
                        (equal (cadr x) 1)
                        (integerp (caddr (cadr fm)))
                        (< (caddr (cadr fm)) -1)
                        (alike1 (cadr (car x)) (cadr (cadr fm)))
                        (not (member ($csign (cadr (car x)))
                                     '($complex imaginary))))
                   ;; 1/x^n*abs(x) -> 1/(x^(n-2)*abs(x)), where n an integer
                   ;; Replace 1/x^n -> 1/x^(n-2)
                   (setq temp (power (cadr (cadr fm))
                                     (add (caddr (cadr fm)) 2)))
                   (rplacd fm (cddr fm))
                   (if (not (equal temp 1))
                       (rplacd fm (cons temp (cdr fm))))
                   ;; Multiply factor 1/abs(x) into list of products.
                   (setq x (list (car x) -1))
                   (setq temp (power (car x) (cadr x)))
                   (setq w (cadr x))
                   (go start))
                  
                  ((and (not (atom (car x)))
                        (eq (caar (car x)) 'mabs)
                        (equal (cadr x) -1)
                        (integerp (caddr (cadr fm)))
                        (> (caddr (cadr fm)) 1)
                        (alike1 (cadr (car x)) (cadr (cadr fm)))
                        (not (member ($csign (cadr (car x)))
                                     '($complex imaginary))))
                   ;; x^n/abs(x) -> x^(n-2)*abs(x), where n an integer.
                   ;; Replace x^n -> x^(n-2)
                   (setq temp (power (cadr (cadr fm)) 
                                     (add (caddr (cadr fm)) -2)))
                   (rplacd fm (cddr fm))
                   (if (not (equal temp 1))
                       (rplacd fm (cons temp (cdr fm))))
                   ;; Multiply factor abs(x) into list of products.
                   (setq x (list (car x) 1))
                   (setq temp (power (car x) (cadr x)))
                   (setq w (cadr x))
                   (go start))
                  
                  ((and (not (atom (cadr fm)))
                        (not (atom (cadr (cadr fm))))
                        (eq (caaadr (cadr fm)) 'mabs)
                        (equal (caddr (cadr fm)) -1)
                        (integerp (cadr x))
                        (> (cadr x) 1)
                        (alike1 (cadadr (cadr fm)) (car x))
                        (not (member ($csign (cadadr (cadr fm)))
                                     '($complex imaginary))))
                   ;; 1/abs(x)*x^n -> x^(n-2)*abs(x), where n an integer.
                   ;; Replace 1/abs(x) -> abs(x)
                   (setq temp (cadr (cadr fm)))
                   (rplacd fm (cddr fm))
                   (rplacd fm (cons temp (cdr fm)))
                   ;; Multiply factor x^(n-2) into list of products.
                   (setq x (list (car x) (add (cadr x) -2)))
                   (setq temp (power (car x) (cadr x)))
                   (setq w (cadr x))
                   (go start))
                  
                  ((or (maxima-constantp (car x))
                       (maxima-constantp (cadadr fm)))
                   (if (great temp (cadr fm))
                       (go gr)))
                  ((great (car x) (cadadr fm))
                   (go gr)))
            (go less))
           ((alike1 (car x) (cadr fm))
            (go equ))
          ((mnump temp)
           ;; When a number goto start and look in the next term.
           (setq fm (cdr fm))
           (go start))
           
           ((and (not (atom (cadr fm)))
                 (eq (caar (cadr fm)) 'mabs)
                 (integerp (cadr x))
                 (< (cadr x) -1)
                 (alike1 (cadr (cadr fm)) (car x))
                 (not (member ($csign (cadr (cadr fm)))
                                     '($complex imaginary))))
            ;; abs(x)/x^n -> 1/(x^(n-2)*abs(x)), where n an integer.
            ;; Replace abs(x) -> 1/abs(x).
            (setq temp (power (cadr fm) -1))
            (rplacd fm (cddr fm))
            (rplacd fm (cons temp (cdr fm)))
            ;; Multiply factor x^(-n+2) into list of products.
            (setq x (list (car x) (add (cadr x) 2)))
            (setq temp (power (car x) (cadr x)))
            (setq w (cadr x))
            (go start))
           
           ((maxima-constantp (car x))
            (when (great temp (cadr fm))
              (go gr)))
           ((great (car x) (cadr fm))
            (go gr)))
  less
     (cond ((mnump temp)
           ;; Multiply a number into the list of products.
           (return (rplaca y (timesk (car y) temp))))
           ((and (eq (car x) '$%i)
                 (fixnump w))
            (go %i))
           ((and (eq (car x) '$%e)
                 $numer
                 (integerp w))
            (return (rplaca y (timesk (car y) (exp (float w))))))
           ((and (onep1 w)
                 (not (constant (car x))))
            (go less1))                  
           ;; At this point we will insert a mexpt expression,
           ;; but first we look at the car of the list of products and
           ;; modify the expression if we found a rational number.
           ((and (mexptp temp)
                 (not (onep1 (car y)))
                 (or (integerp (car y))
                     (ratnump (car y))))
            ;; Multiplying bas^k * num/den.
            (let ((num (num1 (car y)))
                  (den (denom1 (car y)))
                  (bas (car x)))
              (cond ((and (integerp bas)
                          (not (eql 1 (abs bas)))
                          (setq expo (exponent-of (abs num) bas)))
                     ;; We have bas^m*bas^k.
                     (setq temp (power bas (add (cadr x) expo)))
                     ;; Set fm to have 1/denom term.
                     (setq x (div (div num (exptrl bas expo)) den)))
                    ((and (integerp bas)
                          (not (eql 1 (abs bas)))
                          (setq expo (exponent-of den bas)))
                     (setq expo (- expo))
                     ;; We have bas^(-m)*bas^k.
                     (setq temp (power bas (add (cadr x) expo)))
                     ;; Set fm to have the numerator term.
                     (setq x (div num (div den (exptrl bas (- expo))))))
                    (t
                     ;; The rational doesn't contain any (simple) powers of
                     ;; the exponential term.  We're done.
                     (return (cdr (rplacd fm (cons temp (cdr fm)))))))
              ;; Add in the a^(m+k) or a^(k-m) term.
              (setf y (rplaca y 1))
              (rplacd fm (cons temp (cdr fm)))
              (setq temp x
                    x (list x 1)
                    w 1
                    fm y)
              (go start)))
           ((and (maxima-constantp (car x))
                 (do ((l (cdr fm) (cdr l)))
                     ((null (cdr l)))
                   (when (and (mexptp (cadr l))
                              (alike1 (car x) (cadadr l)))
                     (setq fm l)
                     (return t))))
            (go start))
           ((or (and (mnump (car x))
                     (mnump w))
                (and (eq (car x) '$%e)
                     $%emode
                     (among '$%i w)
                     (among '$%pi w)
                     (setq u (%especial w))))
            (setq x (cond (u)
                          ((alike (cdr check) x)
                           check)
                          (t
                           (exptrl (car x) w))))
            (cond ((mnump x)
                   (return (rplaca y (timesk (car y) x))))
                  ((mtimesp x)
                   (go times))
                  ((mexptp x)
                   (return (cdr (rplacd fm (cons x (cdr fm))))))
                  (t
                   (setq temp x
                         x (list x 1)
                         w 1
                         fm y)
                   (go start))))
           ((onep1 w)
            (go less1))
           (t
            (setq temp (list '(mexpt) (car x) w))
            (setq temp (eqtest temp (or check '((foo)))))
            (return (cdr (rplacd fm (cons temp (cdr fm)))))))
  less1
     (return (cdr (rplacd fm (cons (car x) (cdr fm)))))
  gr
     (setq fm (cdr fm))
     (go start)
  equ
     (cond ((and (eq (car x) '$%i) (equal w 1))
            (rplacd fm (cddr fm))
            (return (rplaca y (timesk -1 (car y)))))
           ((zerop1 (setq w (plsk 1 w)))
            (go del))
           ((and (mnump (car x)) (mnump w))
            (return (rplaca (cdr fm) (exptrl (car x) w))))
           ((maxima-constantp (car x))
            (go const)))
  spcheck
     (setq z (list '(mexpt) (car x) w))
     (cond ((alike1 (setq x (simplifya z t)) z)
            (return (rplaca (cdr fm) x)))
           (t
            (rplacd fm (cddr fm))
            (setq rulesw t)
            (return (muln (cons x y) t))))
  const
     (rplacd fm (cddr fm))
     (setq x (car x) check nil)
     (go top)
  times
     (setq z (tms x 1 (setq temp (cons '(mtimes) y))))
     (return (cond ((eq z temp)
                    (cdr z))
                   (t
                    (setq rulesw t) z)))
  del
     (return (rplacd fm (cddr fm)))
  %i
     (if (minusp (setq w (rem w 4)))
         (incf w 4))
     (return (cond ((zerop w)
                    fm)
                   ((= w 2)
                    (rplaca y (timesk -1 (car y))))
                   ((= w 3)
                    (rplaca y (timesk -1 (car y)))
                    (rplacd fm (cons '$%i (cdr fm))))
                   (t
                    (rplacd fm (cons '$%i (cdr fm))))))))

  ;;this doesn't work..
#+ignore
(defun timesin (x y w)                  ; Multiply X^W into Y
  (prog (fm temp z check u expo)
     (if (mexptp x) (setq check x))
     ;; Prepare the factor x^w and initialize the work of timesin
  (cond
   ((and $ratinf (or
		  ($ratextended_p x)
		  ($ratextended_p y)))  ;; not enough. x may be regular, y may be 0/0 etc
    (print 'hi)


    ;;;;  broken for 1/0 *xxx
    ;; fill in more here
    ;; if x is oo and signum(w)>0 then oo*signum(y)
    ;; if x is -oo and uh, w is odd then -oo*signum(y)
    ;; if x is -oo and w is even then oo*signum(y)
    ;; if x is indef then indef
    (cond (($ratind_p x) (return (list *ratind)))
	  ((or ($ratinf_p y)($ratinf_p x)) (return (list *ratinf))) ;; unless oo* zero?
	  (t '$incomplete))))
  top
   (cond
    ((equal w 1)
     (setq temp x))
    (t
     (setq temp (cons '(mexpt) (if check 
                                   (list (cadr x) (mult (caddr x) w))
                                 (list x w))))
     (if (and (not timesinp) (not (eq x '$%i)))
         (let ((timesinp t))
           (setq temp (simplifya temp t))))))
     (setq x (if (mexptp temp)
                 (cdr temp)
                 (list temp 1)))
     (setq w (cadr x)
           fm y)
  start
     ;; Go through the list of terms in fm and look what is to do.
     (cond ((null (cdr fm))
            ;; The list of terms is empty. The loop is finshed.
            (go less))
           ((or (and (mnump temp)
                     (not (or (integerp temp)
                              (ratnump temp))))
                (and (integerp temp)
                     (equal temp -1)))
            ;; Stop the loop for a float or bigfloat number, or number -1.
            (go less))
           ((mexptp (cadr fm))
            (cond ((alike1 (car x) (cadadr fm))
                   (cond ((zerop1 (setq w (plsk (caddr (cadr fm)) w)))
                          (go del))
                         ((and (mnump w)
                               (or (mnump (car x))
                                   (eq (car x) '$%i)))
                          (rplacd fm (cddr fm))
                          (cond ((mnump (setq x (if (mnump (car x))
                                                    (exptrl (car x) w)
                                                    (power (car x) w))))
                                 (return (rplaca y (timesk (car y) x))))
                                ((mtimesp x)
                                 (go times))
                                (t
                                 (setq temp x
                                       x (if (mexptp x) (cdr x) (list x 1)))
                                 (setq w (cadr x)
                                       fm y)
                                 (go start))))
                         ((maxima-constantp (car x))
                          (go const))
                         ((onep1 w)
                          (cond ((mtimesp (car x))
                                 ;; A base which is a mtimes expression. Remove
                                 ;; the factor from the lists of products.
                                 (rplacd fm (cddr fm))
                                 ;; Multiply the factors of the base with
                                 ;; the list of all remaining products.
                                 (setq rulesw t)
                                 (return (muln (nconc y (cdar x)) t)))
                                (t (return (rplaca (cdr fm) (car x))))))
                         (t
                          (go spcheck))))
                  ;; At this place we have to add code for a rational number
                  ;; as a factor to the list of products.
                  ((and (onep1 w)
                        (or (ratnump (car x))
                            (and (integerp (car x))
                                 (not (onep (car x))))))
                   ;; Multiplying bas^k * num/den
                   (let ((num (num1 (car x)))
                         (den (denom1 (car x)))
                         (bas (second (cadr fm))))
                     (cond ((and (integerp bas)
                                 (not (eql 1 (abs bas)))
                                 (setq expo (exponent-of (abs num) bas)))
                            ;; We have bas^m*bas^k = bas^(k+m).
                            (setq temp (power bas
                                              (add (third (cadr fm)) expo)))
                            ;; Set fm to have 1/denom term.
                            (setq x (mul (car y)
                                         (div (div num
                                                   (exptrl bas expo))
                                              den))))
                           ((and (integerp bas)
                                 (not (eql 1 (abs bas)))
                                 (setq expo (exponent-of den bas)))
                            (setq expo (- expo))
                            ;; We have bas^(-m)*bas^k = bas^(k-m).
                            (setq temp (power bas
                                              (add (third (cadr fm)) expo)))
                            ;; Set fm to have the numerator term.
                            (setq x (mul (car y)
                                         (div num
                                              (div den
                                                   (exptrl bas (- expo)))))))
                           (t
                            ;; Next term in list of products.
                            (setq fm (cdr fm))
                            (go start)))
                     ;; Add in the bas^(k+m) term or bas^(k-m)
                     (setf y (rplaca y 1))
                     (rplacd fm (cddr fm))
                     (rplacd fm (cons temp (cdr fm)))
                     (setq temp x
                           x (list x 1)
                           w 1
                           fm y)
                     (go start)))
                  ((and (not (atom (car x)))
                        (eq (caar (car x)) 'mabs)
                        (equal (cadr x) 1)
                        (integerp (caddr (cadr fm)))
                        (< (caddr (cadr fm)) -1)
                        (alike1 (cadr (car x)) (cadr (cadr fm)))
                        (not (member ($csign (cadr (car x)))
                                     '($complex imaginary))))
                   ;; 1/x^n*abs(x) -> 1/(x^(n-2)*abs(x)), where n an integer
                   ;; Replace 1/x^n -> 1/x^(n-2)
                   (setq temp (power (cadr (cadr fm))
                                     (add (caddr (cadr fm)) 2)))
                   (rplacd fm (cddr fm))
                   (if (not (equal temp 1))
                       (rplacd fm (cons temp (cdr fm))))
                   ;; Multiply factor 1/abs(x) into list of products.
                   (setq x (list (car x) -1))
                   (setq temp (power (car x) (cadr x)))
                   (setq w (cadr x))
                   (go start))
                  
                  ((and (not (atom (car x)))
                        (eq (caar (car x)) 'mabs)
                        (equal (cadr x) -1)
                        (integerp (caddr (cadr fm)))
                        (> (caddr (cadr fm)) 1)
                        (alike1 (cadr (car x)) (cadr (cadr fm)))
                        (not (member ($csign (cadr (car x)))
                                     '($complex imaginary))))
                   ;; x^n/abs(x) -> x^(n-2)*abs(x), where n an integer.
                   ;; Replace x^n -> x^(n-2)
                   (setq temp (power (cadr (cadr fm)) 
                                     (add (caddr (cadr fm)) -2)))
                   (rplacd fm (cddr fm))
                   (if (not (equal temp 1))
                       (rplacd fm (cons temp (cdr fm))))
                   ;; Multiply factor abs(x) into list of products.
                   (setq x (list (car x) 1))
                   (setq temp (power (car x) (cadr x)))
                   (setq w (cadr x))
                   (go start))
                  
                  ((and (not (atom (cadr fm)))
                        (not (atom (cadr (cadr fm))))
                        (eq (caaadr (cadr fm)) 'mabs)
                        (equal (caddr (cadr fm)) -1)
                        (integerp (cadr x))
                        (> (cadr x) 1)
                        (alike1 (cadadr (cadr fm)) (car x))
                        (not (member ($csign (cadadr (cadr fm)))
                                     '($complex imaginary))))
                   ;; 1/abs(x)*x^n -> x^(n-2)*abs(x), where n an integer.
                   ;; Replace 1/abs(x) -> abs(x)
                   (setq temp (cadr (cadr fm)))
                   (rplacd fm (cddr fm))
                   (rplacd fm (cons temp (cdr fm)))
                   ;; Multiply factor x^(n-2) into list of products.
                   (setq x (list (car x) (add (cadr x) -2)))
                   (setq temp (power (car x) (cadr x)))
                   (setq w (cadr x))
                   (go start))
                  
                  ((or (maxima-constantp (car x))
                       (maxima-constantp (cadadr fm)))
                   (if (great temp (cadr fm))
                       (go gr)))
                  ((great (car x) (cadadr fm))
                   (go gr)))
            (go less))
           ((alike1 (car x) (cadr fm))
            (go equ))
          ((mnump temp)
           ;; When a number goto start and look in the next term.
           (setq fm (cdr fm))
           (go start))
           
           ((and (not (atom (cadr fm)))
                 (eq (caar (cadr fm)) 'mabs)
                 (integerp (cadr x))
                 (< (cadr x) -1)
                 (alike1 (cadr (cadr fm)) (car x))
                 (not (member ($csign (cadr (cadr fm)))
                                     '($complex imaginary))))
            ;; abs(x)/x^n -> 1/(x^(n-2)*abs(x)), where n an integer.
            ;; Replace abs(x) -> 1/abs(x).
            (setq temp (power (cadr fm) -1))
            (rplacd fm (cddr fm))
            (rplacd fm (cons temp (cdr fm)))
            ;; Multiply factor x^(-n+2) into list of products.
            (setq x (list (car x) (add (cadr x) 2)))
            (setq temp (power (car x) (cadr x)))
            (setq w (cadr x))
            (go start))
           
           ((maxima-constantp (car x))
            (when (great temp (cadr fm))
              (go gr)))
           ((great (car x) (cadr fm))
            (go gr)))
  less
     (cond ((mnump temp)
           ;; Multiply a number into the list of products.
           (return (rplaca y (timesk (car y) temp))))
           ((and (eq (car x) '$%i)
                 (fixnump w))
            (go %i))
           ((and (eq (car x) '$%e)
                 $numer
                 (integerp w))
            (return (rplaca y (timesk (car y) (exp (float w))))))
           ((and (onep1 w)
                 (not (constant (car x))))
            (go less1))                  
           ;; At this point we will insert a mexpt expression,
           ;; but first we look at the car of the list of products and
           ;; modify the expression if we found a rational number.
           ((and (mexptp temp)
                 (not (onep1 (car y)))
                 (or (integerp (car y))
                     (ratnump (car y))))
            ;; Multiplying bas^k * num/den.
            (let ((num (num1 (car y)))
                  (den (denom1 (car y)))
                  (bas (car x)))
              (cond ((and (integerp bas)
                          (not (eql 1 (abs bas)))
                          (setq expo (exponent-of (abs num) bas)))
                     ;; We have bas^m*bas^k.
                     (setq temp (power bas (add (cadr x) expo)))
                     ;; Set fm to have 1/denom term.
                     (setq x (div (div num (exptrl bas expo)) den)))
                    ((and (integerp bas)
                          (not (eql 1 (abs bas)))
                          (setq expo (exponent-of den bas)))
                     (setq expo (- expo))
                     ;; We have bas^(-m)*bas^k.
                     (setq temp (power bas (add (cadr x) expo)))
                     ;; Set fm to have the numerator term.
                     (setq x (div num (div den (exptrl bas (- expo))))))
                    (t
                     ;; The rational doesn't contain any (simple) powers of
                     ;; the exponential term.  We're done.
                     (return (cdr (rplacd fm (cons temp (cdr fm)))))))
              ;; Add in the a^(m+k) or a^(k-m) term.
              (setf y (rplaca y 1))
              (rplacd fm (cons temp (cdr fm)))
              (setq temp x
                    x (list x 1)
                    w 1
                    fm y)
              (go start)))
           ((and (maxima-constantp (car x))
                 (do ((l (cdr fm) (cdr l)))
                     ((null (cdr l)))
                   (when (and (mexptp (cadr l))
                              (alike1 (car x) (cadadr l)))
                     (setq fm l)
                     (return t))))
            (go start))
           ((or (and (mnump (car x))
                     (mnump w))
                (and (eq (car x) '$%e)
                     $%emode
                     (among '$%i w)
                     (among '$%pi w)
                     (setq u (%especial w))))
            (setq x (cond (u)
                          ((alike (cdr check) x)
                           check)
                          (t
                           (exptrl (car x) w))))
            (cond ((mnump x)
                   (return (rplaca y (timesk (car y) x))))
                  ((mtimesp x)
                   (go times))
                  ((mexptp x)
                   (return (cdr (rplacd fm (cons x (cdr fm))))))
                  (t
                   (setq temp x
                         x (list x 1)
                         w 1
                         fm y)
                   (go start))))
           ((onep1 w)
            (go less1))
           (t
            (setq temp (list '(mexpt) (car x) w))
            (setq temp (eqtest temp (or check '((foo)))))
            (return (cdr (rplacd fm (cons temp (cdr fm)))))))
  less1
     (return (cdr (rplacd fm (cons (car x) (cdr fm)))))
  gr
     (setq fm (cdr fm))
     (go start)
  equ
     (cond ((and (eq (car x) '$%i) (equal w 1))
            (rplacd fm (cddr fm))
            (return (rplaca y (timesk -1 (car y)))))
           ((zerop1 (setq w (plsk 1 w)))
            (go del))
           ((and (mnump (car x)) (mnump w))
            (return (rplaca (cdr fm) (exptrl (car x) w))))
           ((maxima-constantp (car x))
            (go const)))
  spcheck
     (setq z (list '(mexpt) (car x) w))
     (cond ((alike1 (setq x (simplifya z t)) z)
            (return (rplaca (cdr fm) x)))
           (t
            (rplacd fm (cddr fm))
            (setq rulesw t)
            (return (muln (cons x y) t))))
  const
     (rplacd fm (cddr fm))
     (setq x (car x) check nil)
     (go top)
  times
     (setq z (tms x 1 (setq temp (cons '(mtimes) y))))
     (return (cond ((eq z temp)
                    (cdr z))
                   (t
                    (setq rulesw t) z)))
  del
     (return (rplacd fm (cddr fm)))
  %i
     (if (minusp (setq w (rem w 4)))
         (incf w 4))
     (return (cond ((zerop w)
                    fm)
                   ((= w 2)
                    (rplaca y (timesk -1 (car y))))
                   ((= w 3)
                    (rplaca y (timesk -1 (car y)))
                    (rplacd fm (cons '$%i (cdr fm))))
                   (t
                    (rplacd fm (cons '$%i (cdr fm))))))))



;;;;fixed BUGS 4/13/16
#|  3.0^(1/0),  3.0^(0/0)  fixed
(0/0)^0  comes out indef  as does (0^0)/(0^0)

;;;; fixed bugs 2/22/2022  sin(0/0)is indef
;; bug 1/(1/0)  is 0 fixed 2/22/22
;; bug 1/(-1/0) is -0 fixed 2/22/22  ((rat simp) 0 -1)
;;  fixed 1/(-0) is -oo

;; bugs  x* (0/0)   should be 0/0
;;       x/ (0/0)  should be 0/0

;; bug or feature:?? float(0/0) error

|#


;;; where is this?  maybe try to keep types if cl has a builtin bigfloat???? 

(defun cl-or-bfloat-binary-op (f1 f2 arg1 arg2)(declare (ignore f1))
       (funcall f2 arg1 arg2))
