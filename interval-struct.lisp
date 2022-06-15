(in-package :maxima)

;; extended real interval, already in maxima as structure ri, printed as interval(..)

#| There is a natural tension with interval representation in a CAS between

(1) Implementing the most logically efficient endpoint representation as
IEEE double-float objects, numbers and Not-a-Numbers. And that's all.

(2) Implementing the most general computable representation which would
include the above, but others. To be specific include:
a. IEEE floats
b. Arbitrary-precision floats 
c. Integers (arbitrary precision)
d. Rationals (arbitrary precision)
e. extra symbols as necessary, +oo, -oo, undefined. maybe e, pi.
f. (definitelynot going here...) symbolic expressions e.g. x^2+1

Also including tags for decorations as proposed in IEEE standard 1788

My belief is that version (1) and (2-b) semantics for IEEE 1788 may be
implemented by linking to a load module from N. Revol, MPFI

versions
|#

#+ignore ;;
(defstruct (ri (:constructor ri (lo hi))
	       (:print-function (lambda (p stream k)
				  (declare (ignore k))
				  (format stream "{~a..~a}"  (ri-lo p)(ri-hi p)))))
  lo hi ) ;;

(defstruct (ri (:constructor ri (lo hi))
	       (:print-function (lambda (p stream k)
				  (declare (ignore k))
				  (format stream "{~a..~a}"  (mstring (ri-lo p))
					  (mstring (ri-hi p))))))
  lo hi )

;; define string formatted version for wxmaxima

;; (%i1)   interval(1,2)
;; should display as  {1..2}  in wxmaxima, also


(defun wxxml-interval(x l r)
  (wxxml-atom (format nil "~a"  (apply '$interval  (cdr x))); the CL printer formats it
	      l r))

#+ignore
(defun wxxml-interval(x l r)
  (wxxml-atom (mformat nil "~m"  (apply '$interval  (cdr x))); the CL printer formats it
	     l r)) ;; allow rational number endpoints, e.g. 1/2

(defprop $interval wxxml-interval wxxml)


;; REDEFINE mnump addk, timesk exptb exptrl  from simp.lisp
;;  telling maxima that an interval is a number is not a winner if it can't do arithmetic on it.
;; need trivial changes in unknown number of places.


(defmfun mnump (x) ;; new
  (cond ((atom x)( or (numberp x)(ri-p x)))
	;; not an atom
	((and (listp x) (listp (car x)))
	 (member (caar x) '(rat bigfloat)))
	( t nil)))


(defun addk (x y) ;; new
  (cond ((eql x 0) y)
	((eql y 0) x)
	((and (numberp x) (numberp y)) (+ x y))
	((or ($bfloatp x) ($bfloatp y)) ($bfloat (list '(mplus) x y)))
	;;;
	((or (ri-p x) (ri-p y)) ($intervalplus_2 x y));;; only change
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

(defun timesk (x y)     ; X and Y are assumed to be already reduced
  (cond ((equal x 1) y)
	((equal y 1) x)
	((and (numberp x) (numberp y)) (* x y))
	((or (ri-p x) (ri-p y)) ($intervaltimes_2 x y));;; only change
	((or ($bfloatp x) ($bfloatp y)) ($bfloat (list '(mtimes) x y)))
	((floatp x) (* x (fpcofrat y)))
	((floatp y) (* y (fpcofrat x)))
	(t (timeskl x y))))

;; 

(defun exptb (a b)
  (cond ((and(ri-p a)(numberp b)) ($intervalmexpt a b)) ;; only change
	 ((equal a %e-val)
	 ;; Make B a float so we'll get double-precision result.
         (exp (float b)))
        ((or (floatp a) (not (minusp b)))
         #+gcl
         (if (float-inf-p (setq b (expt a b)))
             (merror (intl:gettext "EXPT: floating point overflow."))
             b)
         #-gcl
         (expt a b))
	(t
	 (setq b (expt a (- b)))
	 (*red 1 b))))

(defun exptrl (r1 r2)
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
	 (cond ((or (zerop1 r2) (mnegp r2))
		(if (not errorsw)
		    (merror (intl:gettext "expt: undefined: ~M") (list '(mexpt) r1 r2))
		    (throw 'errorsw t)))
	       (t (zerores r1 r2))))
	((or (zerop1 r2) (onep1 r1))
	 (cond ((or ($bfloatp r1) ($bfloatp r2)) bigfloatone)
	       ((or (floatp r1) (floatp r2)) 1.0)
	       (t 1)))
	((or ($bfloatp r1) ($bfloatp r2)) ($bfloat (list '(mexpt) r1 r2)))
	((and (numberp r1) (integerp r2)) (exptb r1 r2))
	((and (numberp r1) (floatp r2) (equal r2 (float (floor r2))))
	 (exptb (float r1) (floor r2)))
	((and(ri-p r1)(numberp r2))  ($intervalmexpt r1 r2)) ;;only change
	((or $numer (and (floatp r2) (or (plusp (num1 r1)) $numer_pbranch)))
	 (let (y  #+kcl(r1 r1) #+kcl(r2 r2))
	   (cond ((minusp (setq r1 (addk 0.0 r1)))
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
		 (t (exp (* r2 (log r1)))))))
	((floatp r2) (list '(mexpt simp) r1 r2))
	((integerp r2)
	 (cond ((minusp r2)
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
			       (list '(rat simp) (- (caddr r1)) (- (cadr r1))))
			      (t (list '(rat simp) (caddr r1) (cadr r1))))
			(- r2)))
	       (t (list '(rat simp) (exptb (cadr r1) r2) (exptb (caddr r1) r2)))))
	((and (floatp r1) (alike1 r2 '((rat) 1 2)))
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
;;;;;;;;;;;;;;;;;;;;

    

(defun $interval(a b) (ri a b)) ; should do some error checks...

(defun $intervalp(r)(ri-p r))

(defmethod $intervalplus_2((r ri) (s ri))
  ($interval (+ (ri-lo r)(ri-lo s))  ;; fix for roundings
	     (+ (ri-hi r)(ri-hi s))))

;; just a few two-argument versions of plus and times

(defmethod $intervalplus_2((r ri) (s integer))  ;;[a,b]+c -> [a+c,b+c]
   ($interval (+ (ri-lo r)s)  ;; fix for roundings
	      (+ (ri-hi r) s)))
;;
;; Controversial since lisp or other float may tarnish exactness

(defmethod $intervalplus_2((r ri) (s t))  ;;[a,b]+c -> [a+c,b+c]
  (if (mnump s)
   ($interval (add (ri-lo r)s)  ;; fix for roundings
	      (add (ri-hi r) s))
   `((mplus) ,r ,s)))

(defmethod $intervalplus_2((s t)(r ri) )  ;; args reversed.
  (if (mnump s)
   ($interval (add (ri-lo r)s)  ;; fix for roundings
	      (add (ri-hi r) s))
   `((mplus) ,r ,s)))

;;;;;;;;;;;;;;;;;;;;;

(defmethod $intervalplus_2((s integer)(r ri) )  ;; args reversed.
   ($interval (+ (ri-lo r)s)  ;; fix for roundings
	     (+ (ri-hi r) s)))

(defmethod $intervalplus_2((r t) (s t))  ;; any other rules?
  `((mplus simp) ,r ,s))

(defmethod
  $intervaltimes_2((r ri) (s number))
  (if (> s 0)
      ($interval 
       (* (ri-lo r)s)  ;; fix for roundings
       (* (ri-hi r) s))
   ($interval   ;; s is negative 
    (* (ri-hi r) s)
    (* (ri-lo r)s))))

  (defmethod $intervaltimes_2( (s number) (r ri))  
    ($intervaltimes_2 r s))

;; added 6/30/2021 RJF

(defmethod $intervaltimes_2((r ri) (s ri)) 
  ;; could be sped up if rl>0, sl>0 etc 
  ;; if we are doing maxima bigfloats etc  need to do maxima compare tho'
  (let* ((rl (ri-lo r))
	 (rh (ri-hi r))
	 (sl (ri-lo s))
	 (sh (ri-hi s))
	 (p1 (* rl sl))
	 (p2 (* rl sh))
	 (p3 (* rh sl))
	 (p4 (* rh sh)))
    ($interval(min p1 p2 p3 p4);;  (meval (list  ('$min) p1 p2 p3 p4))
	      (max p1 p2 p3 p4);; ditto
	      ))) ;; roundings?

;;
;; added 7/3/2021 RJF

(defmethod $interval_max_2((r number)(s number)) (max r s))
(defmethod $interval_max_2((r ri)(s number)) (max (ri-hi r) s))
(defmethod $interval_max_2((s number)(r ri)) (max (ri-hi r) s))
(defmethod $interval_max_2((r ri)(s ri)) (max (ri-hi r) (ri-hi s)))

(defmethod $interval_min_2((r number)(s number)) (min r s))
(defmethod $interval_min_2((r ri)(s number)) (min (ri-lo r) s))
(defmethod $interval_min_2((s number)(r ri)) (min (ri-lo r) s))
(defmethod $interval_min_2((r ri)(s ri)) (min (ri-lo r) (ri-lo s)))

(defprop $interval_min $interval_min_2 $interval_op)
(defprop $interval_max $interval_max_2 $interval_op)

;; we also have to figure out how to make interval_min(123) -> 123
(defun $interval_min_1(r) r)
(defun $interval_max_1(r) r)

;; this would have to be called explicitly. note, x-x would otherwise be simplified via
;; x + (-x)  and the identity of x is lost, so x-x is not zero.
;; Thaat is, if x is a..b,  x-x comes out as a-b.. b-a rather than 0. This
;; can fix it, if you explicitly call intervaldiff(x,x)..
;; interval difference

(defmethod $intervaldiff((r ri)(s ri)) (if (eq r s) 0
					 ($intervalplus_2 r
							  ($intervaltimes_2 -1 s))))

;***********

 (defmethod $intervalmexpt(  (r ri) (s integer))  
   (cond ((oddp s)
	  (let ((a (expt (ri-lo r) s))	;fix for roundings
		(b (expt (ri-hi r) s)))
	    ($interval (min a b)(max a b))))
	 ((< (ri-lo r) 0 (ri-hi r))
	  ($interval 0 (expt (ri-hi r) s)))
	 ((< 0 (ri-lo r))
	  (let ((a (expt (ri-lo r) s))	;fix for roundings
		(b (expt (ri-hi r) s)))
	    ($interval (min a b)(max a b))))
	 ((> (ri-lo r)  0)
	  (let ((a (expt (abs(ri-lo r)) s))	;fix for roundings
		(b (expt (abs(ri-hi r)) s)))
	    ($interval (min a b)(max a b))))))
	 
;;; uh, for even, have to be careful, e.g.  {-1..1}^2  is {0..1}
;;;     (error "~s^~s not programmed yet " r s) ;; fix this later?


;; This handles exp(interval).  

(defmethod $intervalmexpt((r (eql '$%e)) (s ri))
  (let ((a (exp (ri-lo s))) ;fix for roundings
	(b (exp (ri-hi s))))
    ($interval (min a b)(max a b))))

  

(defmethod $intervalmexpt ((r t)(s t))	; leftover cases
  `((mexpt simp) ,($interval r s))) ; should be simplified already

(defun $intervalsimp(r)
  (cond ((atom r) r)
	((member (caar r) '(mplus mtimes $interval_min $interval_max)) ;; add here other n-ary stuff

	 (let((intparts nil)
	      (otherparts nil)
	      (argsimp (mapcar '$intervalsimp (cdr r)))
	      (res (if (eq (caar r) 'mtimes) 1 0)) ;identity
	      (intop (get (caar r) '$interval_op)))

	   (if (null intop) ;; if no interval procedure for this op, do this
	       (return-from $intervalsimp
		 (simplifya  (cons (list (caar r))argsimp) nil)))
	      
	   (loop for i in argsimp do
		 ;; separate the pieces, putting all items that
		 ;; might combine with intervals in the intparts stack
		 
		 (cond ((or (ri-p i)($numberp i)) (push i intparts))
		       (t (push i otherparts))))
	   
	   (if (or (null intparts)(null (cdr intparts)))
	       ;; maybe nothing to do at this level
	       ;;if only 0 or 1 intparts
	       ;; if there is a 1-op version, find it and apply here.
	       ;;;****** patch here for interval_min_1,  max
	       (return-from $intervalsimp
		 (simplifya (cons (list (caar r))argsimp) nil)))
	   
	   (loop for i in intparts do
		 (setf res (funcall intop res i))) ;combine 2 at a time
	   (simplifya (cons (list(caar r)) (cons res otherparts)) nil)
	   ))
	(t (let 
	       ((argsimp (mapcar '$intervalsimp (cdr r)))
		(intop (get (caar r) '$interval_op)))
	     ;;(format t "~% intop=~s, argsimp=~s~%" intop argsimp)
	     (simplifya
	      (if intop (apply intop argsimp)
		;; if no interval procedure for this op, do this
		(cons (list (caar r))argsimp))
		
	      nil)))))

(defprop mexpt $intervalmexpt $interval_op)
(defprop mplus $intervalplus_2 $interval_op)
(defprop mtimes $intervaltimes_2 $interval_op)


;; need to add programs for every other operation
;; and every kind of argument and endpoints: float, rat, integer
;; and fix the rounding modes. 
;; e.g. intervalsimp( z^2); 
;;  sin, cos, divide, max, comparisons

#| examples:
interval(1,2) -interval(1,2) 		;
intervalsimp(%)  /*should be interval(-1,1) */			;
x:interval(1,2) 			;
intervalsimp(x^2) 			;  
x-x					;
intervalsimp(%)  /* should be 0 */ ;       

|#

#| One way of how to do sin, (analogous for cos..)

reduce lo  to standard range 0 to 2 pi  by adding adjustment V
adjust hi  by adding V as well.

if lo<= pi/2 <= hi,  then res_hi = 1
if lo<= 3*pi/2 <= hi  then res_lo= -1

otherwise, sin is monotonic in the range, so
res_lo = sin(lo)  unless it is already -1,  rounding down
res_hi = sin(hi) unless it is already 1. rounding up

return interval(res_lo, res_hi)
|#


(defun reduce-range-mpi-pi(x)
  (let((r (mod x (* 2 pi))))  ;reduce to monotonic range -pi to pi
    (if (> r pi) (- r pi) r)))

(defun $rrp(x)(reduce-range-mpi-pi x))
				 
;; this is totally inaccurate if |x| > 2^53 since we don't have pi to enough digits

#+ignore

(defmethod interval-sin((r ri))
  (let* ((lo (ri-lo r))
	 (hi (ri-hi ))
	 (z ))))

    
