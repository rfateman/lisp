;;; -*- mode: lisp; package: maxima; base: 10; syntax: common-lisp; -*-
;;;>
;;;> *************************************************************************************
#|  02/03/20202 RJF

This is a reworking of Poisson series to make it
 more general (no limit on coefficients)
 consequently slower and less space efficient than the version of 1974
but still much faster than general representation.

Here's an article c. 1974 about this by RJF, specifically about the predecessor
of this package
https://link.springer.com/article/10.1007/BF01227622
emphasizing that for large enough series, storing the terms in a
linear list is inferior to trees.

A far more recent paper in J. Symb. Comp.
https://www.sciencedirect.com/science/article/pii/S0747717100903961
does not mention the previous article; presumably a failure of refereeing.



A Poisson form is really a sum of two parts, a sine series and a cosine series.
Each is a hash table ... (make-hash-table)
where the entries are a dotted pair of outer-coefficient and (make-array k  :element-type 'integer).
Here k is the number of atomic names in  poisvars, a list of parameters
in the trig arguments.
Thus  if poisvars = [u,v,w,x,y,z] then the term (r/25)*sin(3*u+445*z) would be represented
by an entry in the sine hash-table at key (binary number) #b 100001 of  (expr . #(3 0 0 0 0 445)),
where expr is the internal representation in Maxima of r/25, namely
((MTIMES SIMP) ((RAT SIMP) 1 25) $R) 
k=6, the default number of argument parameters, is apparently
enough in previous sample applications involving orbital calculations.

The facilities needed are conversion to/from general representation,
addition/subtraction, multiplication, and a subtle kind of 
substitution/ approximation.

supported commands

poisvars()  or maybe better is  poisinit(vars,optional element type of coefs)
					;   e.g.  poisvars(u,v,w); poisinit([u,v,w], integer)
					;what types?  maxpos value e.g. 15? do we allow general expr.?
intopois() 				; e.g. intopois (sin(3*u)^3)
outofpois()
poissubst(a,b,c) 	


  Substitutes a for b in c.  c is a Poisson series.
  (1) Where b is a variable in poisvars, e.g. u, v, w, x, y, or z, then
   a must be an expression linear in those variables (e.g., '6*u +
   4*v').
  (2) Where b is other than those variables, then a must also be
  free of those variables, and furthermore, free of sines or cosines.
  'poissubst (a, b, c, d, n)' is a special type of
  substitution which operates on a and b as in type (1) above,
  but where d is a Poisson series, expands 'cos(d)' and
  'sin(d)' to order n so as to provide the result of substituting
  'a + d' for b in c.  The idea is that d is an expansion
  in terms of a small parameter.  For example, 'poissubst (u, v,
  cos(v), %e, 3)' yields 'cos(u)*(1 - %e^2/2) - sin(u)*(%e - %e^3/6)'.

to add, multiply, compute powers of a Poisson series, do
intopois (R*S), intopois (R+S) etc.

The display of Poisson series will have /P/ next to the line label.

Incidentally, the name honors the distinguished French mathematician Simeon Denis Poisson
b. 1781, who apparently had nothing to do with this particular type
of computation.

|#

;;;< revised to here 2/03/2020



(in-package :maxima)

;;
;;; replacing both poisvars and poislim.
;;; the default is poisinit([u,v,w,x,y,z], 5)
;;; meaning arguments of trig function are  (a*u+b*v+.+f*z) where |a| etc <2^5.

;; general poisson series

(proclaim '(special *argc *coef poisvals poisco1 poiscom1 b* a* *a ;ss cc h* rwg 5/90
		    poishift poistsm poissiz poists $wtlvl *pois1* $poisvars maxpoiscoef))

(defvar *poisz* '((mpois simp) (make-hash-table)(make-hash-table)))
(defvar trim nil) ;; don't trim terms.

;; we are given, for example, r = $u vars=((mlist) $u $v ...) vals = (1 32 ... 33554432)
	
(defun $poissimp (x)
  (if (mbagp x) (cons (car x) (mapcar #'$poissimp (cdr x)))
    ($outofpois x)))

;; (declare-top(fixnum ae poishift poistsm poissiz poists)) ;rjf
;; this declaration above could be restored for an increase in speed
;; if we can guarantee that poislim is small enough. 

;;; this tells the evaluator to keep out of poisson series.

(defprop mpois (lambda (x) x) mfexpr*) 

(defun $poisplus (a b)  ;; add 2 PS.  intopois(a+b+c) calls this.
       (setq a (intopois a) b (intopois b))
       (list '(mpois simp) 
	     (poismerge22 (cadr a) (cadr b)) 
	     (poismerge22 (caddr a) (caddr b)))) 

(proclaim '(special *b *fn)) 

(defun $poismap (p sinfn cosfn)  ;; what does this do?  not documented, not used.
       (prog (*b *fn) 
             (setq p (intopois p))
             (setq *fn (list sinfn))
             (return (list (car p)
                           (poismap (cadr p))
                           (prog2 (setq *fn (list cosfn)) (poismap (caddr p))))))) 

(defun poismap (y) ;; um, maps over the object y. uses dynamic vars *b *fn bound above
       (cond ((null y) nil)
             (t (setq *b (meval (list *fn (poiscdecode (cadr y)) (poisdecodec (car y)))))
                (tcons3(car y) (intopoisco  *b) (poismap (cddr y))))))

;; test to see if 2 arrays are of same length and equal content.
;; could be done by map/
;;(reduce #'and (map 'list #'(lambda( p q)(= p q)) r s))
(defun equal-ar (r s &aux count) 
  (if
      (and (arrayp r)(arrayp s)(=(setf count(length r))(length s)))
      (progn (loop for i from 0 to (1- count)  do 
		   (if (not(= (aref r i)(aref s i)))
		       (return-from equal-ar nil)
		       ))
	     t)
    nil)				; not arrays of same length
  )

(defun poismerge22 (r s) 
       (cond ((null r) s)
	     ((null s) r)
	     ((equal (car r) (car s))
	      (prog (tt) 
	       (setq tt (poisco+ (cadr r) (cadr s)))
	       (return (cond ((poispzero tt) (poismerge22 (cddr r) (cddr s)))
			     (t (cons (car s) (cons tt (poismerge22 (cddr r) (cddr s)))))))))
	     ((< (car r) (car s)) (cons (car r) (cons (cadr r) (poismerge22 (cddr r) s))))
	     (t (cons (car s) (cons (cadr s) (poismerge22 (cddr s) r)))))) 

(defun poiscosine (m) 
       (setq m (poisencode m))
       (cond ((poisnegpred m) (setq m (poischangesign m))))
       (list '(mpois simp) nil (list m poisco1))) 

(defun poissine (m) 
       (setq m (poisencode m))
       (cond ((poisnegpred m) (list '(mpois simp) (list (poischangesign m) poiscom1) nil))
	     (t (list '(mpois simp) (list m poisco1) nil)))) 

(defun $intopois (x) (prog (*a) (return (intopois x)))) 

(defun intopois (a) 
       (cond ((atom a)
	      (if (equal a 0)
		  *poisz*
		  (list '(mpois simp) nil (list poishift (intopoisco a)))))
	     ((eq (caar a) 'mpois) a)
	     ((eq (caar a) '%sin) (poissine (cadr a)))
	     ((eq (caar a) '%cos) (poiscosine (cadr a)))
	     ((and (eq (caar a) 'mexpt)   ;; power of a pois series
		   (numberp (caddr a)) 
		   (> (caddr a) 0))
	      ($poisexpt (intopois (cadr a)) (caddr a)))
	     ((eq (caar a) 'mplus) ;; sum of pois series
	      (setq *a (intopois (cadr a)))
	      (mapc (function (lambda (z) (setq *a ($poisplus *a (intopois z))))) (cddr a))
	      *a)
	     ((eq (caar a) 'mtimes)
	      (setq *a (intopois (cadr a)))
	      (mapc (function (lambda (z) (setq *a ($poistimes *a (intopois z))))) (cddr a))
	      *a)
	     ((eq (caar a) 'mrat) (intopois (ratdisrep a)))
	     (t (list '(mpois simp) nil (list poishift (intopoisco a)))))) 

(defun tcons (r s) (cond ((poispzero (car s)) (cdr s)) (t (cons r s)))) 

(defun poisnegpred (n) 
  (prog (r) 
     loop   	(cond ((equal n 0.) (return nil)))
	(setq r (- (mod n poists) poistsm))
	(cond ((equal r 0)(setq n (truncate n poists))(go loop))
	      ( t (return (> 0 r)))))) 

(defun poischangesign (n) (- (* poishift 2.) n)) 

(defun oldpoisencode (h &aux l)	
  (setq l (errset (checkencode h $poisvars poisvals)))
  (cond ((atom l)
	 (merror "illegal argument to poisson series form:~%~m" h))
	(t (car l))))

;; for testing
#+ignore
(defun pe(h)
  (poisencode1 h $poisvars))
(defun pe2 (h)(poisencode2 h))
;; real program
  
(defun poisencode (r)
  (poisencode2 r $poisvars poisvals))

#+ignore
(defun poisencode1(h pv) (let ((ans nil) tt (save h))
			(loop for ii in (cdr pv) do 
			      (setf tt ($bothcoef h ii))
			      (setf h (simplifya (third tt)nil)) ; the rest of the expression
			     ;; (format t "~% h=~s ans=~s" h ans)
			      (push (list '(mlist)  ii (second tt))
				    ans))
			(if (eql h 0) (cons '(mlist)(nreverse ans))
			  (merror  "~%encoding of Poisson trig argument ~m has failed. 
Left-over expression ~m is not expressible as a linear combination of terms in poisvars= ~m " save h pv))))


;; try to extract the integer coefficients of poisvars, default u,v,w,x,y,z
;; and multiply them by appropriate shifts to fit them into a single integer.

(defun poisencode2(h pv vals) 
  (let ((ans 0) tt (save h) theco)
    (loop for ii in (cdr pv) and jj in vals do 
	  (setf tt ($bothcoef h ii))
	  (setf h (simplifya (third tt)nil)) ; the rest of the expression
	  ;; (format t "~% h=~s ans=~s" h ans)
	  ;; here we have to check that (second tt) is a legitimate
	  ;; integer coefficient in the right range.
	  (setf theco (second tt))
	  (if (and (integerp theco) (<= (abs theco) maxpoiscoef))
	  ;; Since it is, we include it in the encoding 
	      (setf ans (+ ans (* theco jj)))
	    (merror "~% Poisson trig coefficent ~m in ~m is not an integer in [-~m,  ~m]" 
		    theco save maxpoiscoef maxpoiscoef)))
    (if (eql h 0) ans  ;; make sure there's nothing left over
      (merror  "~%encoding of Poisson trig argument ~m has failed. 
Left-over expression ~m is not expressible as a linear combination of terms in poisvars= ~m " 
	       save h pv))))

			    

(defun poislim1 (u bits) ;;u is ignored. this is called when $poisinit is called.
  ;; bits is the total number of bits to be used for coefficients.
  ;; if there are 5 variables and bits =30, then there are 30/5 = 6 bits each
  ;; allowing for +-2^5 or +-32 in the coefficient field.
  ;; keeping bits less than a fixnum length should speed things up.
  (prog (n lim)
	(cond
	 ((not (typep bits 'fixnum))
	  (merror "improper value for poislim:~%~m" bits)))
	(cond
	 ((> 30 bits)
	  (mformat t "poisson series are using 30 bits, anyway") ;;rjf
	 ))
    (setq n (truncate (max bits 30) (length (cdr $poisvars))))
    
    (mformat t "maximum poisson coefficient is +-~m~%"
		 (setf maxpoiscoef (1- (expt 2 (1- n)))))
    (mformat t "for each of the variables in ~m ~%" $poisvars)
	(setq poisvals nil)
	(setq poists (expt 2 n))
	(setq lim (+ (length $poisvars) -2))
	(do ((j 0 (1+ j)))
	    ((> j lim))
	  (setq poisvals (cons (expt poists j) poisvals)))
    (setq poisvals (reverse poisvals))
	(setq poissiz
	      n
	      poistsm
	      (expt 2 (1- n))
	      poishift
	      (prog (sum)
		    (setq sum 0)
		    (do ((i 0 (1+ i)))
			((> i lim))
		      (setq sum (+ sum (* poistsm (expt poists i)))))
		    (return sum))
	      *poisz* '((mpois simp) nil nil)
	      *pois1* (list '(mpois simp) nil (list poishift 1)))
	n))

(defun poisdecodec (h) 
  (prog (arg vars) 
	(setq vars (cdr $poisvars))
	loop
	(setq arg (cons
		   (list '(mtimes) 
			 (- (mod h poists) poistsm) (car vars) )
		   arg))
	(setq vars(cdr vars) h (truncate h poists))
	(cond((null vars)(return (simplifya (cons '(mplus) arg) nil)))
	     (t (go loop)))))
	      
;;; this program multiplies a poisson series p by a non-series, c,
;;; which is free of sines and cosines .

(defun $poisctimes (c p) 
 (list '(mpois simp) (poisctimes1 (setq c (intopoisco c)) (cadr p))(poisctimes1 c (caddr p))))

 
(defun $outofpois (p) 
       (prog (ans) 
	     (cond ((or (atom p) (not (eq (caar p) 'mpois))) (setq p (intopois p))))

	     ;; do sines
	     (do ((m (cadr p) (cddr m)))
		 ((null m))
	       (setq ans (cons (list '(mtimes)
				     (poiscdecode (cadr m))
				     (list '(%sin) (poisdecodec (car m))))
			       ans)))

	     ;; do cosines
	     (do ((m (caddr p) (cddr m)))
		 ((null m))
	       (setq ans (cons (list '(mtimes)
				     (poiscdecode (cadr m))
				     (cond ((equal (car m) poishift) 1.)
					   (t (list '(%cos) (poisdecodec (car m))))))
			       ans)))
	     (return (cond ((null ans) 0.) (t (simplifya (cons '(mplus) ans) nil)))))) 

(declare-top (special $pfeformat)) ;rjf fix

(defun $printpois (p)
       (prog ($pfeformat)
	     (setq $pfeformat t);; typically there are lots of fractions;
	     (setq p (intopois p))

	     ;; do sines
	     (do ((m (cadr p) (cddr m)))
		 ((null m))
	       (displa (simplifya (list '(mtimes)
					(poiscdecode (cadr m))
					(list '(%sin) (poisdecodec (car m))))
				  t)))

	     ;; do cosines
	     (do ((m (caddr p) (cddr m)))
		 ((null m))
	       (displa (simplifya (list '(mtimes)
					(poiscdecode (cadr m))
					(cond ((equal (car m) poishift) 1)
					      (t (list '(%cos) (poisdecodec (car m))))))
				  t)))
	     (return '$done))) 


;;; $poisdiff differentiates a poisson series wrt 
;;; an element on  $poisvars (default x, y, z, u, v, w), or a coeff var.


(proclaim '(special m))

(defun $poisdiff (p m)
  (setq p (intopois p))
  (cond((mexp-member m $poisvars) (list (car p) (cosdif (caddr p) m) (sindif (cadr p) m)))
       (t (list (car p)(poisdif4(cadr p))(poisdif4 (caddr p))))))


(defun poisdif4(y)
  (cond((null y) nil)
       (t (tcons3 (car y)(poiscodif (cadr y) m) (poisdif4 (cddr y))))))


;;; cosdif differentiates cosines to get sines

(defun cosdif (h m) 
       (cond ((null h) nil)
	     (t (tcons (car h)
		       (cons (poisco* (intopoisco (minus (poisxcoef (car h) m))) (cadr h))
			     (cosdif (cddr h) m)))))) 

(defun sindif (h m) 
       (cond ((null h) nil)
	     (t (tcons (car h)
		       (cons (poisco* (intopoisco (poisxcoef (car h) m)) (cadr h))
			     (sindif (cddr h) m)))))) 



(defun poisxcoef (h m) 
  (- (mod (truncate h
				   (expt poists (pois-where m (cdr $poisvars))))
			 poists)
	      poistsm))

(defun pois-where(m l)(pois-where1 m l 0))

(defun pois-where1(m l num)
  (cond ((alike1 m (car l) ) num) ;; got it
	((null l)nil);; error: not found
	(t(pois-where1 m (cdr l) (1+ num)))))

(defun nonperiod (p)
  (and (null (cadr p)) (= (caaddr p) poishift) (null (cddr (caddr p))))) 


;;; avl balanced tree search and insertion.
;;; node looks like (key (llink .  rlkink) balancefactor .  record)
;;; program follows algorithm given in knuth vol. 3 455-57

(proclaim '(special ans)) 

;; macros to extract fields from node
;;; try these (from pois2).  
(defmacro key   (x) `(car   ,x))
(defmacro llink (x) `(caadr ,x)) 
(defmacro rlink (x) `(cdadr ,x))
(defmacro bp    (x) `(caddr ,x))
(defmacro rec   (x) `(cdddr ,x))

;;; try these (from pois2).
(defmacro order< (&rest args) `(< ,@args))
(defmacro order= (&rest args) `(= ,@args))

(defmacro setrlink (x y) `(setf (rlink ,x) ,y))
(defmacro setllink (x y) `(setf (llink ,x) ,y))
(defmacro setbp    (x y) `(setf (bp    ,x) ,y))
(defmacro setrec   (x y) `(setf (rec   ,x) ,y))

(defun insert-it (pp newrec) (setrec pp (poisco+ (rec pp) newrec))) 

(defun avlinsert (k newrec head)
       (prog (qq tt ss pp rr) 
	     (setq tt head)
	     (setq ss (setq pp (rlink head)))
	a2   (cond ((order< k (key pp)) (go a3))
		   ((order< (key pp) k) (go a4))
		   (t (insert-it pp newrec) (return head)))
	a3   (setq qq (llink pp))
	     (cond ((null qq) (setllink pp (cons k (cons (cons nil nil) (cons 0. newrec))))
		    (go a6))
		   ((order= 0. (bp qq)) nil)
		   (t (setq tt pp ss qq)))
	     (setq pp qq)
	     (go a2)
	a4   (setq qq (rlink pp))
	     (cond ((null qq) (setrlink pp (cons k (cons (cons nil nil) (cons 0. newrec))))
		    (go a6))
		   ((order= 0. (bp qq)) nil)
		   (t (setq tt pp ss qq)))
	     (setq pp qq)
	     (go a2)
	a6   (cond ((order< k (key ss)) (setq rr (setq pp (llink ss))))
		   (t (setq rr (setq pp (rlink ss)))))
	a6loop
	     (cond ((order< k (key pp)) (setbp pp -1.) (setq pp (llink pp)))
		   ((order< (key pp) k) (setbp pp 1.) (setq pp (rlink pp)))
		   ((order= k (key pp)) (go a7)))
	     (go a6loop)
	a7   (cond ((order< k (key ss)) (go a7l)) (t (go a7r)))
	a7l  (cond ((order= 0. (bp ss)) (setbp ss -1.) (setllink head (1+ (llink head)))
		    (return head))
		   ((order= (bp ss) 1.) (setbp ss 0.) (return head)))
	     (cond ((order= (bp rr) -1.) nil) (t (go a9l)))
	     (setq pp rr)
	     (setllink ss (rlink rr))
	     (setrlink rr ss)
	     (setbp ss 0.)
	     (setbp rr 0.)
	     (go a10)
	a9l  (setq pp (rlink rr))
	     (setrlink rr (llink pp))
	     (setllink pp rr)
	     (setllink ss (rlink pp))
	     (setrlink pp ss)
	     (cond ((order= (bp pp) -1.) (setbp ss 1.) (setbp rr 0.))
		   ((order= (bp pp) 0.) (setbp ss 0.) (setbp rr 0.))
		   ((order= (bp pp) 1.) (setbp ss 0.) (setbp rr -1.)))
	     (setbp pp 0.)
	     (go a10)
	a7r  (cond ((order= 0. (bp ss)) (setbp ss 1.) (setllink head (1+ (llink head)))
		    (return head))
		   ((order= (bp ss) -1.) (setbp ss 0.) (return head)))
	     (cond ((order= (bp rr) 1.) nil) (t (go a9r)))
	     (setq pp rr)
	     (setrlink ss (llink rr))
	     (setllink rr ss)
	     (setbp ss 0.)
	     (setbp rr 0.)
	     (go a10)
	a9r  (setq pp (llink rr))
	     (setllink rr (rlink pp))
	     (setrlink pp rr)
	     (setrlink ss (llink pp))
	     (setllink pp ss)
	     (cond ((order= (bp pp) 1.) (setbp ss -1.) (setbp rr 0.))
		   ((order= (bp pp) 0.) (setbp ss 0.) (setbp rr 0.))
		   ((order= (bp pp) -1.) (setbp ss 0.) (setbp rr 1.)))
	     (setbp pp 0.)
	a10  (cond ((eq ss (rlink tt)) (setrlink tt pp)) (t (setllink tt pp)))
	     (return head))) 

(defun avlinit (key rec) 
  (cons 'top (cons (cons 0. (cons key (cons (cons nil nil) (cons 0. rec)))) (cons 0. nil)))) 


;; untree converts the tree to a list which looks like ( smallest-key record next-smallest-key record ....  largest-key
;;record)

(defun untree (h) (prog (ans) (untree1 (rlink h)) (return ans))) 

(defun untree1 (h) 
       (cond ((null h) ans)
	     ((null (rlink h)) (setq ans (tcons3 (key h) (rec h) ans)) (untree1 (llink h)))
	     (t (setq ans (tcons3 (key h) (rec h) (untree1 (rlink h)))) (untree1 (llink h))))) 

(defun tcons3 (r s tt) (cond ((poispzero s) tt) (t (cons r (cons s tt))))) 


(defun poismerges (a ae l) 
       (cond ((= poishift ae) l)				       ; sine(0) is 0
	     ((poisnegpred ae) (poismerge (poisco* poiscom1 a) (poischangesign ae) l))
	     (t (poismerge a ae l)))) 

(defun poismergec (a ae l) 
       (cond ((poisnegpred ae) (poismerge a (poischangesign ae) l)) (t (poismerge a ae l)))) 

(defun poismerge (a ae l) (cond ((poispzero a) nil) (t (merge11 a ae l)))) 

(defun poismerge2 (r s) 
       (cond ((null r) s)
	     ((null s) r)
	     (t (prog (m n tt) 
		      (setq m (setq n (cons 0. r)))
		 a    (cond ((null r) (rplacd m s) (return (cdr n)))
			    ((null s) (return (cdr n)))
			    ((equal (car r) (car s))
			     (setq tt (poisco+ (cadr r) (cadr s)))
			     (cond ((poispzero tt)
				    (rplacd m (cddr r)) (setq r (cddr r) s (cddr s)))
				   (t
				    (rplaca (cdr r) tt)
				    (setq s (cddr s) r (cddr r) m (cddr m)))))
			    ((> (car r) (car s))
			     (rplacd m s)
			     (setq s (cddr s))
			     (rplacd (cddr m) r)
			     (setq m (cddr m)))
			    (t (setq r (cddr r)) (setq m (cddr m))))
		      (go a))))) 

(defun merge11 (a ae l) (poismerge2 (list ae a) l)) 

(defun poismergesx (a ae l) 
       (cond ((equal poishift ae) l)				       ; sine(0) is 0
	     ((poisnegpred ae) (avlinsert (poischangesign ae) (poisco* poiscom1 a) l))
	     (t (avlinsert ae a l)))) 

(defun poismergecx (a ae l) 
       (cond ((poisnegpred ae) (avlinsert (poischangesign ae) a l)) (t (avlinsert ae a l)))) 


(proclaim '(special trim poiscom1 poishift)) 

(defun poisctimes1 (c h) 
       (cond ((null h) nil)
             ((and trim (trimf (car h))) (poisctimes1 c (cddr h)))
             (t (tcons (car h) (cons (poisco* c (cadr h)) (poisctimes1 c (cddr h))))))) 

(defun trimf (m)
  (meval (cons '($poistrim) (mapcar (function (lambda(v)(poisxcoef m v)))
				    (cdr $poisvars)))))

(defun $poistimes (a b) 
  (prog (slc clc temp ae aa zero trim t1 t2 f1 f2) 
	(setq a (intopois a) b (intopois b))
	(cond ((or (getl '$poistrim '(expr subr)) (mget '$poistrim 'mexpr))
	       (setq trim t)))
	(cond ((nonperiod a) (return ($poisctimes (cadr (caddr a)) b)))
	      ((nonperiod b) (return ($poisctimes (cadr (caddr b)) a))))
	(setq slc (avlinit poishift (setq zero (intopoisco 0.))) clc (avlinit poishift zero))
	;; proceed through all the sines in argument a
	(do ((sla (cadr a) (cddr sla)))
	    ((null sla))
	  (setq aa (halve (cadr sla)) ae (car sla))
	  ;; sine(u)*sine(v) ==> (-cosine(u+v) + cosine(u-v))/2
	  ;; it would be good if we checked for overflow of the bits
	  ;; by testing under mask.  Later version, maybe.
	  (do ((slb (cadr b) (cddr slb)))
	      ((null slb))
	    (setq t1 (plus ae poishift (minus (car slb)))
		  t2 (plus ae (minus poishift) (car slb)))
	    (cond(trim(setq f1(trimf t1) f2 (trimf t2)))
		 (t (setq f1 nil f2 nil)))
	    (setq temp (poisco* aa (cadr slb)))
	    (cond ((poispzero temp) nil)
		  (t (or f1 (poismergecx temp t1 clc))
		     (or f2 (poismergecx (poisco* poiscom1 temp) t2 clc)))))
	  ;; sine*cosine ==> sine + sine
	  (do ((clb (caddr b) (cddr clb)))
	      ((null clb))
	    (setq t1 (plus ae poishift (minus (car clb)))
		  t2 (plus ae (minus poishift) (car clb)))
	    (cond(trim(setq f1(trimf t1) f2 (trimf t2)))
		 (t (setq f1 nil f2 nil)))
	    (setq temp (poisco* aa (cadr clb)))
	    (cond ((poispzero temp) nil)
		  (t
		   (or f1 (poismergesx temp t1 slc)) (or f2 (poismergesx temp t2 slc))))))
	;; proceed through all the cosines in argument a
	(do ((cla (caddr a) (cddr cla)))
	    ((null cla))
	  (setq aa (halve (cadr cla)) ae (car cla))
	  ;; cosine*sine ==> sine - sine
	  (do ((slb (cadr b) (cddr slb)))
	      ((null slb))
	    (setq t1 (plus ae poishift (minus (car slb)))
		  t2 (plus ae (minus poishift) (car slb)))
	    (cond(trim(setq f1(trimf t1)
			    f2 (trimf t2)))
		 (t (setq f1 nil f2 nil)))
	    (cond 
	      (t (setq temp (poisco* aa (cadr slb)))
		 (cond ((poispzero temp) nil)
		       (t (or f1 (poismergesx (poisco* poiscom1 temp) t1 slc))
			  (or f2 (poismergesx temp t2 slc)))))))
	  ;; cosine*cosine ==> cosine + cosine
	  (do ((clb (caddr b) (cddr clb)))
	      ((null clb))
	    (setq t1 (plus ae poishift (minus (car clb)))
		  t2 (plus ae (minus poishift) (car clb)))
	    (cond (trim (setq f1 (trimf t1) f2 (trimf t2)))
		  (t (setq f1 nil f2 nil)))
	    (cond 
	      (t (setq temp (poisco* aa (cadr clb)))
		 (cond ((poispzero temp) nil)
		       (t (or f1 (poismergecx temp t1 clc))
			  (or f2 (poismergecx temp t2 clc))))))))
	(return (list '(mpois simp) (untree slc) (untree clc)))))

(defun $poisexpt (p n) 
       (prog (u h) 
	     (if (or (not (integerp n)) (minusp n))
		 (improper-arg-error '$poisexpt n))
	     (if (oddp n) (setq u p) (setq u (setq h (intopois 1))))
	a    (setq n (lsh n -1))
	     (if (zerop n) (return u))
	     (setq p ($poistimes p p))
	     (if (oddp n) (setq u (if (equal u h) p ($poistimes u p))))
	     (go a)))

(defun $poissquare (a) ($poisexpt a 2))

(proclaim '(special m))

;;; $poisint integrates a poisson series wrt x,y, z, u, v, w.  the variable of
;;; integration must occur only in the arguments of sin or cos,
;;; or only in the coefficients.  poiscointeg is called to integrate coeffs.

;;; non-periodic terms are removed.

(defun $poisint (p m) 
  (prog (b*) (setq p (intopois p))
	(cond ((mexp-member m (cdr $poisvars))
	       (return (list (car p) (cosint* (caddr p) m) (sinint* (cadr p) m))))
	      (t (return (list (car p)(poisint4 (cadr p))(poisint4 (caddr p)))))))) 

(defun poisint4 (y)
  (cond ((null y) nil)
	(t (tcons3 (car y) (poiscointeg (cadr y) m) (poisint4 (cddr y))))))

;;;cosint* integrates cosines to get sines

(defun cosint* (h m) 
  (cond ((null h) nil)
	((equal 0. (setq b* (poisxcoef (car h) m))) (cosint* (cddr h) m))
	(t (tcons (car h)
		  (cons (poisco* (intopoisco (list '(mexpt) b* -1.)) (cadr h))
			(cosint* (cddr h) m)))))) 

(defun sinint* (h m) 
  (cond ((null h) nil)
	((equal 0. (setq b* (poisxcoef (car h) m))) (sinint* (cddr h) m))
	(t (tcons (car h)
		  (cons (poisco* (intopoisco (list '(mexpt) (minus (poisxcoef (car h) m)) -1.))
				 (cadr h))
			(sinint* (cddr h) m)))))) 


;;; $poissubst substitutes an expression for a variable in argument of trig functions or
;;; coefficients.

(defun poissubsta (a b* c
		   &aux (h* (- (poisencode (list '(mplus) a (list '(mtimes) -1. b*)))
					poishift))
			ss cc)
  (labels ((poissubst1s (c)
	    (when c (setq ss (poismerges (cadr c) (argsubst (car c)) ss))
		    (poissubst1s (cddr c))))
	   (poissubst1c (c)
	    (when c (setq cc (poismergec (cadr c) (argsubst (car c)) cc))
		    (poissubst1c (cddr c))))
	   (argsubst (c) (plus c (* h* (poisxcoef c b*)))))
    (poissubst1s (cadr c))
    (poissubst1c (caddr c))
    (list (car c) ss cc)))

;; From the Franz Lisp version:
;(defmfun $poissubst n ()
;  (cond ((not (or (equal n 3.) (equal n 5.))) (merror  "wrong number of args to poissubst"))
;	((equal n 5.)
;	 (fancypoissubst (arg 1.) (arg 2.) (intopois (arg 3.)) (intopois (arg 4.)) (arg 5.)))
;	(t
;	 ((lambda (a* b* c)
;	    (cond ((mexp-member b* (cdr $poisvars)) (poissubsta a* b* c))
;		  (t (list (car c) (poissubstco1 (cadr c)) (poissubstco1 (caddr c))))))
;	    (arg 1.)
;	    (arg 2.)
;	    (intopois (arg 3.))))))

;;; From KMP's version...
(defun $poissubst (a* b* c &rest d-and-n)
  (case (length d-and-n)
    (0
      (let ((c (intopois c)))
	(cond ((mexp-member b* (cdr $poisvars)) (poissubsta a* b* c))
	      (t (list (car c) (poissubstco1 (cadr c)) (poissubstco1 (caddr c)))))))
    (2
      (fancypoissubst a* b* (intopois c) (intopois (nth 0 d-and-n)) (nth 1 d-and-n)))
    (otherwise (wrong-number-of-args-error '$poissubst))))

(defun poissubstco1 (c) 
       (cond ((null c) nil)
	     (t (tcons (car c) (cons (poissubstco a* b* (cadr c)) (poissubstco1 (cddr c)))))))

(defun fancypoissubst (a b* c d n &aux h* (anz (list '(mpois simp) nil nil))
				       (dc (intopois 1.)) (ds (intopois 0.))
				       *argc *coef)
  "substitutes a+d for b in c, where d is expanded in powerseries to order n"
  (when (equal n 0.) (return-from fancypoissubst ($poissubst a b* c)))
  (setq d (intopois d))
  (labels ((fancypois1s (dp n lim)
	    "dp is last power: d^(n-1), lim is highest to go"
	    (cond ((> n lim) nil)
		  (t (setq ds ($poisplus ds
					 ($poisctimes (list '(rat)
							    (expt -1. (truncate (1- n) 2.))
							    (factorial n))
						      (setq dp ($poistimes dp d)))))
		     (fancypois1c dp (1+ n) lim))))
	   (fancypois1c (dp n lim)
	    "dp is last power: d^(n-1), lim is highest to go"
	    (cond ((> n lim) nil)
		  (t (setq dc ($poisplus dc ($poisctimes (list '(rat)
							       (expt -1. (truncate n 2.))
							       (factorial n))
							 (setq dp ($poistimes dp d)))))
		     (fancypois1s dp (1+ n) lim))))
	   (fancypac (c)
	    "cos(r+k*b) ==> k*cos(r+k*a)*dc - k*sin(r+k*a)*ds"
	    (prog ()
		  (cond ((null c) (return nil)))
		  (setq *coef (poisxcoef (car c) b*))
		  (cond ((equal *coef 0.)
			 (setq anz ($poisplus anz (list '(mpois simp) nil
							    (list (car c) (cadr c)))))
			 (go end)))
		  (cond ((poispzero (setq *coef (poisco* (cadr c) (intopoisco *coef))))
			 (go end)))
		  (setq *argc (argsubst (car c)))
		  (setq anz
			($poisplus
			  anz
			  ($poisplus ($poistimes (list '(mpois simp)
						       nil
						       (poismergec *coef *argc nil))
						 dc)
				     ($poistimes (list '(mpois simp)
						       (poismerges (poisco* poiscom1 *coef)
								   *argc nil)
						       nil)
						 ds))))
	       end (fancypac (cddr c))))
	   (fancypas (c) 
	    "sin(r+k*b) ==> k*cos(r+k*a)*ds + k*sin(r+k*a)*dc"
	    (prog nil 
		  (cond ((null c) (return nil)))
		  (setq *coef (poisxcoef (car c) b*))
		  (cond ((equal *coef 0.)
			 (setq anz
			       ($poisplus anz
					  (list '(mpois simp) (list (car c) (cadr c)) nil)))
			 (go end)))
		  (cond ((poispzero (setq *coef (poisco* (cadr c) (intopoisco *coef))))
			 (go end)))
		  (setq *argc (argsubst (car c)))
		  (setq anz ($poisplus anz
					 ($poisplus ($poistimes (list '(mpois simp)
								      nil
								      (poismergec *coef *argc
										  nil))
								ds)
						    ($poistimes (list '(mpois simp)
								      (poismerges *coef *argc
										  nil)
								      nil)
								dc))))
	       end (fancypas (cddr c))))
	   (argsubst (c) (plus c (* h* (poisxcoef c b*)))))
    (fancypois1s 1. 1. n)
    (setq h* (- (poisencode (list '(mplus) a (list '(mtimes) -1. b*)))
			 poishift))
    (fancypas (cadr c))
    (fancypac (caddr c))
    anz))

; the following comment fragment predates my marauding --rwg 5/90
;argument  do not exceed some predefined bound in absolute value

;;; these are the only coefficient dependent routines. 

;;; poiscdecode decodes a coefficient

(defun poiscdecode (x) x) 


;;; intopoisco puts an expression into poisson coefficient form

(defun intopoisco (x) (simplifya x nil)) 


;;; poisco+ adds 2 coefficients

(defun poisco+ (r s) (add r s)) 


;;; poisco* multiplies 2 coefficients

(defun poisco* (r s) (mul r s)) 


;;; halve divides a coefficient by 2

(defun halve (r) (mul  '((rat) 1. 2.) r)) 


;;; poissubstco substitutes an expression for a variable in a coefficient.

(defun poissubstco (a b c) (substitute a b c)) 

;;; this differentiates a coefficient

(defun poiscodif (h var) (sdiff h var))

;;; this integrates a coefficient
(defun poiscointeg (h var) (intopoisco ($integrate (poiscdecode h) var)))

;;; test for zero

(defun poispzero (x) (zerop1 x)) 

;;; the number 1 in coefficient arithmetic, the number -1

(defvar poisco1 1)
(defvar poiscom1 -1)

(defun $poisinit(vars lim)
  (setf $poisvars vars)			;; 
  (poislim1 nil lim) ;;??  coeffs are lim bits, e.g. 2^lim max
  )

($poisinit '((mlist) $u $v $w $x $y $z) 30)  ;; default set of poisson vars. ;rjf
;; broken, can't load this with last line..