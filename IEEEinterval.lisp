  ;;  A basis for interval arithmetic
;;  constructed by overloading generic arithmetic. 
;;  Richard Fateman, November, 2005
;;  Changed to provide an implementation of IEEE standard intervals, 2/6/2013 RJF
;;  We allow mixed operands, e.g. interval <op> integer, single, rational, double

;;; RI = Real Interval

;;; I happen to be running / testing with Allegro Common Lisp from
;;; Franz.om There is a free version available for download.  Any
;;; other ANSI standard Common Lisp should be able to run code
;;; mostly like this, 

;;; BUT MAY REQUIRE ATTENTION TO IMPLEMENTATION DETAILS.

;;; We expect that all CLs will allow this code but will use different
;;; names for its "system" or "implementation" package.  All
;;; implementations we are aware of allows NaNs and Infinities and
;;; have a way of testing a float for being one of these, but
;;; the details vary.

;;; Standard printing of NaN and Inf is not in the CL standard either.
;;; This is incorporated in the code for naming of
;;; constants *s-inf* etc, and the programs pbg and badguy.

;;; Although it extends even further beyond the CL ANSI standard, this
;;; file contains some code written for SBCL, Steel Bank Common Lisp.
;;; SBCL which provides language hooks for rounding and other IEEE 754
;;; features. See
;;; http://common-lisp.net/~alendvai/darcs/sbcl/src/code/float-trap.lisp
;;; On the other hand, that file warns

;;; :ROUNDING-MODE 
;;; The rounding mode to use when the result is not exact. Possible
;;; values are :NEAREST, :POSITIVE-INFINITY, :NEGATIVE-INFINITY and
;;; :ZERO.  Setting this away from :NEAREST is liable to upset SBCL's
;;; maths routines which depend on it.
;;;

#| 
The design for this implementation is somewhat more general than appears to
be expected in the following ways.

1. Interval endpoints can be any of the following numeric types

single-float, double-float,  oquad-double bigfloat (implemented via MPFR),
exact integer (arbitrary precision) exact rational.  Other number types could
presumably be added so long as they have sufficient operations defined, and
can inter-operate with the other forms. Also allowed are floating-point
Not a Numbers (single and double) as well as positive or negative infinity of
types single and double float.

2. It is not necessary for the endpoints of an interval to have the same
type.

3. Arithmetic combinations of the various numeric types are defined in the
scalar arithmetic systems, and the results in computing the endpoints of
the resulting interval will abide by the default coercions for scalars.
For single <op> double, the results are double.
For exact <op> exact, the result is exact if possible otherwise 
 (as for example sqrt, exp, sin) double.
For single <op> exact, the result is single
For double <op> exact, the result is double

4. The endpoints can always be coerced to other types. An
interval I can be created such that both endpoints are of type T
by (coerce I T),  where T may be 'single-float 'ratio 'double-float etc.
We have not yet implemented for MPFR bigfloat, quad-double and others simply
to avoid having to bring those packages in, also.

5. There is only one constructor function, ri  for Real Interval. It takes
3 arguments:  lower, upper, and decoration.  Decorations are symbols COM,
DAC, DEF, TRV, EMP, ILL. at the moment.

6. There is no text2interval program because I do no believe it has a
practical use in Lisp.  If you want to state a number like 0.1 and mean
1/10 rather than 0.1d0, the closest binary float to 1/10, then you
can just write 1/10.

7. Intervals all have decorations.  By executing (setf *printdecor* nil) you
will not see them printed. 

8. There are a few routines that should be utilized by anyone extending
this package.  Macros with-ri and with-ri2 are used to "unpackage" one
or two real interval arguments, so the details of picking out the parts
are hidden.  The program widen  is like the constructor ri, with 3 arguments.
Any endpoint that is not exact will be bumped in the direction of widening
the interval by a unit in the last place. A zero will be bumped by
an appropriate epsilon; oo will be bumped down to the most-positive float
of that type, etc. for -oo.

9. Programs are expected to be composed in the ordinary functional Lisp
manner, so that (+ a b c (sin (* d e)))
can be executed entirely with interval values for the variables a, b, c, d, e
Or any subset of the variable can be numeric scalars of any (non-complex) type.

Such a program could be executed in the ri (RealInterval) or ga
 (Generic Arithmetic) package.

In order to disambiguate the case of type coercion as
might be necessary, (+ a b c) will be treated as (+ a (+ b c))
and similarly for multiplication.

10. Since I do not understand the full requirements for decorations,
most programs propagate the "worst" of the input decorations. When
a result is empty, the lower and upper bounds are set to double-float NaNs.

Some notes on the underlying lisp arithmetic and relations.

We are trying this out in Allegro Common Lisp. Some of these results
should be the same for any IEEE754 compliant ANSI Common Lisp, but the
Common Lisp standard is relatively agnostic with respect to 754.

If N is a NaN, of any size, single, double, ...?  Then
(op N N) is false for op being =, <, >, <=, >=.   

Be careful because (not (> x y)) is not equivalent to (<= x y).

For arithmetic, +, *, -, /  if any operand is a NaN, the result
is a NaN.  If there are NaNs of different sizes, the widest is used.
No error is signalled.   (however, (expt NaN 0) is 1.0

For arithmetic, +, *, -, /  if any operand is a NaN, the result is a NaN.
No error is signalled.  But beware division by zero: (/ x 0) or (expt 0 neg).
Also beware of excursions into complex plane, e.g. (sqrt neg) or (expt neg f),  -1<f<1.

In the following, there is a type derived for the answer.  we use a shorthand of
0.0 or 1.0  to stand for 0.0e0 or 0.0d0  or 1.0e0 1.0d0.  Which width is used depends
on the widths of the NaNs or Infs in the expression. Choice is for widest of the operands.
The expression is not examined in a unified fashion to pick the widest of all operands
and then coercing everything to widest. Rather, each subexpression is converted as
necessary.  If I understand the downside of this, there could be multiple roundings
as a result, not a desired situation.

For arithmetic, 
Inf*0 is N
Inf-Inf is N
Inf/Inf is N
x/Inf is 0.0 for any x except NaN or Inf
Inf+Inf is Inf

(expt NaN 0) is 1.0
(expt Inf 0) is 1.0
(expt 0 x) is 1.0 for float x unless x<0.0
(expt 0 x) is error for x<= 0.0         ...........
(expt 0.0 0.0) is error                 ............
(expt 0 x) is 1 for integer x or ratio x
(expt 0 0) is 1, in particular
(expt 0.0 0) is 1, also.


(sin N) is N
(sin Inf) is N
etc.

(atan Inf) is 1.5707... pi/2

These defaults look right for the demands of interval arithmetic for
scalar arithmetic except for division by zero  or 0^(negative)

|#

;;(defpackage :ri				;uses generic arithmetic defined in ga.lisp
;;   ... now in packs.lisp )

#-gcl (eval-when (load) (require "ga") (provide "ri"))
(in-package :ri)

;; structure for real interval with decoration.  
;; decoration is a small integer, for ordering purposes
;; COM is 5, DAC is 4, DEF is 3, TRV is 2, EMP is 1, ILL is 0 at the moment
(defconstant COM 5)
(defconstant DAC 4)
(defconstant DEF 3)
(defconstant TRV 2)
(defconstant EMP 1)
(defconstant ILL 0)

(defmacro nan-p(x)
  #+allegro     `(excl::nan-p ,x)
  #+SBCL        `(sb-vm::float-nan-p ,x)
  #+gcl         `(float-nan-p ,x))

(defun nan-pfun(x) ;; sometimes we need a function, not a macro
  #+allegro     (excl::nan-p x)
  #+SBCL        (sb-vm::float-nan-p x)
  #+gcl         (float-nan-p x))

(defmacro inf-p(x)
  #+allegro     `(excl::infinityp ,x)
  #+SBCL        `(sb-vm::float-infinity-p ,x)
  #+gcl          `(float-inf-p ,x))


;;; if *printdecor* is nil, just print bare intervals, no decorations

(defvar *printdecor* t)  

;;; if a rational number e.g. 2/3 must be converted to a float in order to
;;; operate on it, e.g. sin() or log() etc, then what float should be used?
(defvar *preferred-float* 'double-float)


(defstruct (ri (:constructor ri (lo hi &optional (decor 5))))lo hi decor)

(defvar *m1to1* (ri -1 1 DAC))

;; a bare interval prints as [number, number]  e.g. [-1/2, 1/3]  or [0.0d0, 1.0d0]
;; a decorated interval prints as [number, number, /DAC] 

(defvar *printintervalreadablymax* nil) ;; if t, print intervals so they can be read back in by maxima
(defvar *printintervalreadablylisp* nil);; if t, print intervals so they can be read back in by lisp
(defvar *printintervalmidrad* nil) ;; if t, and the others are nil.. print in mid +-rad.

(defmethod print-object ((a ri) stream)
  (cond (*printintervalreadablymax* 
	   (if *printdecor*
	       (format stream "interval(~a,~a, /~a)"  (pbg(ri-lo a))(pbg(ri-hi a))(pdecor (ri-decor a )))
	     (format stream "interval(~a,~a)"  (pbg(ri-lo a))(pbg(ri-hi a)))))
	(*printintervalreadablylisp* 
	 (if *printdecor*
	     (format stream "(ri ~a ~a, /~a)"  (pbg(ri-lo a))(pbg(ri-hi a))(pdecor (ri-decor a )))
	   (format stream "(ri ~a ~a)"  (pbg(ri-lo a))(pbg(ri-hi a)))))
	(*printintervalmidrad* 
	 ;; should test for NaN and inf since [-oo,oo]] otherwise looks like NaN+-NaN, [0,oo] like oo+-oo
	 

	 (let* ((mid (+ (/ (ri-lo a) 2)(/ (ri-hi a) 2)))
		(rad (abs (- mid  (ri-hi a)))) ;; this is the radius.
		;;(ulpmid (* double-float-epsilon mid)) ;; unit in last place of midpoint
		;;(ulpdec (/ (cl::log ulpmid)#.(cl:log 10.0)))
		;;(rad (ceiling dif  ulpdec))
		)
	   (format stream "int(~s+-~s)" mid rad))
	 #+ignore
	 ;;we want to see something like   (1.23+-.005)d4, with no more
	 ;;digits displayed than can be comprehended.
	 ;; maybe (1.230 +-5ulp) d4.
	 ;;
	
	 (let* ((mid (+ (/ (ri-lo a) 2)(/ (ri-hi a) 2)))
		(absrad (abs (- mid  (ri-hi a)))) ;; this is the radius.
		(ulpmid (* double-float-epsilon mid)) ;; unit in last place of midpoint
		(rad (ceiling absrad  ulpmid)) ;; this is not good.
		)
	   (format stream "int(~s+-~sULP)" mid rad))
	 )
	   
	
	(t
	 (if *printdecor*
	     (format stream "[~a,~a, /~a]"  (pbg(ri-lo a))(pbg(ri-hi a))(pdecor (ri-decor a )))
	   (format stream "[~a,~a]"  (pbg(ri-lo a))(pbg(ri-hi a)))))))
	 

(defun ri-mid(m r &optional (dec COM)) ;; midpoint and radius constructor
  (ri (- m r)(+ m r) dec))
			    

;; the next 6 lines define our terms for
;; implementation-dependent names, just in case we need them.
;; These are the allegro names


(defconstant *d-inf* #.(* 2 most-positive-double-float))
(defconstant *s-inf* #.(* 2 most-positive-single-float))

(defconstant *dn-inf* #.(* -2 most-positive-double-float))
(defconstant *sn-inf* #.(* -2 most-positive-single-float))

(defconstant *s-nan* #.(- (- *dn-inf* *dn-inf*)))
(defconstant *d-nan* #.(- (- *dn-inf* *dn-inf*)))

;; just for fun, we can also do this, notationally.
(defconstant oo *d-inf*)  ;; the atom oo
(defconstant -oo *dn-inf*) ;; the atom -oo.  Yes, Lisp allows that to be a symbol name
(defconstant NaN *d-nan*)
(defconstant Inf *d-inf*)
(defconstant -Inf *dn-inf*)

(defun pbg(x) 
  ;; print (possibly) bad guy. Maps all non-usual floats into something printable.
  (cond((inf-p x)
	(if (> x 0)"oo" "-oo"))
       ((nan-p x)"NaN")
       (t  x)))

(defun pdecor(x)
  (case x 
    (5 "COM")  ;; optional?
    (4 "DAC")
    (3 "DEF")  ;; arbitrary coding for setting the order
    (2 "TRV")
    (1 "EMP")
    (0 "ILL")
    (otherwise "illegal decoration")))


(defmacro worse (&rest z)`(min ,@z)) ;; compare 2 or more   decorations 

(defmacro widen(lo hi decor) `(ri (bd ,lo)(bu ,hi) ,decor))


;; See file later for sample of real interval version of sin.
;; Similar code for cos, tan, etc.

;; must figure out =, >, <, union, intersection.

(defmethod ga::intersection ((r ri)(s ri))
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	    (let ((loans(max lo1 lo2))
		  (hians(min hi1 hi2)))
	      (if (< loans hians) (ri loans hians (worse dec1 dec2))
		(ri NaN NaN EMP)))))

(defmethod union ((r ri)(s ri))
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	    (let ((loans(min lo1 lo2))
		  (hians(max hi1 hi2)))
	      ;; do we want to check for gaps between ?
	      (ri loans hians (worse dec1 dec2 )))))


;; = on intervals doesn't make sense unless intervals are 1 point.


;; from Graham, On Lisp, macro hackery
(defun mkstr (&rest args)
  (with-output-to-string (s)(dolist (a args) (princ a s))))

(defun symb (&rest args) (values (intern (apply #'mkstr args))))

(defmacro with-struct ((name . fields) struct &body body)
  (let ((gs (gensym)))
    `(let ((,gs ,struct))
      (let ,(mapcar #'(lambda (f)
			`(,f (,(symb name f) ,gs)))
		    fields)
	,@body))));;; e.g. (with-struct (ri- lo hi) r (f lo hi))
;;; based on...
;;;from Figure 18.3: Destructuring on structures. from On Lisp, P. Graham

;; take 2 real intervals and grab their insides. Then
;; do something with them. sample usage...
;;(with-ri2 ri1 ri2 (lo1 hi1)(lo2 hi2) (ri (+ lo1 lo2)(+ hi1 h2)))
(defmacro with-ri2 (struct1 struct2 names1 names2 &body body)
  (let ((gs1 (gensym))
	(gs2 (gensym)))
    `(let ((,gs1 ,struct1)
	   (,gs2 ,struct2))
       (let ,(append 
	      (mapcar #'(lambda (f field)
			  `(,f (,(symb 'ri- field) ,gs1)))
		      names1
		      '(lo hi decor))
	      (mapcar #'(lambda (f field)
			  `(,f (,(symb 'ri- field) ,gs2)))
		      names2
		      '(lo hi decor)))
	 ,@body))))

(defmacro with-ri (struct1 names1  &body body)
  (let ((gs1 (gensym)))
    `(let ((,gs1 ,struct1))
       (let  ,(mapcar #'(lambda (f field)
			  `(,f (,(symb 'ri- field) ,gs1)))
		      names1
		      '(lo hi decor))
	 ,@body))))

;; version with directed rounding. Always valid but interval has been widened
;; perhaps more than necessary, by ULP rather than half ULP (unit in last place)
;; bd rounds down toward -inf, bu round up toward +inf.

(defmethod ga::two-arg-+ ((r ri)(s ri))
  ;; to be more precise we bump  down for lo, round up 
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	    (widen (+ lo1 lo2)(+ hi1 hi2) (worse dec1 dec2))))

;; SBCL nominally allows the setting of rounding modes and other flags.
;; We hope that the flags are not disturbed by the body of the code.

;; here's the model

#+SBCL 
(defun set-floating-point-modes (x) (sb-vm::set-floating-point-modes x))
#+SBCL 
(defun get-floating-point-modes () (sb-vm::get-floating-point-modes))

#+SBCL
(defmacro with-rounding(direction &rest body) ; direction e.g. :negative-infinity
  (let ((old-modes (gensym)) (res (gensym)))
  `(let ((,old-modes (sb-int:get-floating-point-modes)))
     (sb-int:set-floating-point-modes :rounding-mode ,direction)
     (setq ,res (progn ,@body))
     (apply #'sb-int:set-floating-point-modes ,old-modes)
     ,res)))
#+sbcl
(defmacro bracket ( &rest body) ; both direction for rounding.
  (let ((old-modes (gensym)) (resdown (gensym)) (resup (gensym)))
    `(let ((,old-modes (sb-int:get-floating-point-modes)) 
	   (,resup 0.0d0) 
	   (,resdown 0.0d0) )
       (declare 
	(notinline cl::+ cl::- cl::* cl::/ 
		   cl::expt cl::sin cl::cos 
		   cl::log cl::exp)) ;; need to add everything in body!! how??
     (sb-int:set-floating-point-modes :rounding-mode :negative-infinity)
     (setq ,resdown (progn ,@body))
     (sb-int:set-floating-point-modes :rounding-mode :positive-infinity)
     (setq ,resup (progn ,@body))
     (apply #'sb-int:set-floating-point-modes ,old-modes)
     (list ,resdown ,resup))))


;; if you just wanted to be crude and set the rounding mode regardless of
;; who else might be affected by it or who else might affect it after you set
;; it but before you used it, you could do this:
#+SBCL
(defun upit()    (sb-int:set-floating-point-modes :rounding-mode :positive-infinity))
#+SBCL
(defun dnit()    (sb-int:set-floating-point-modes :rounding-mode :negative-infinity))
#+sbcl
(defun getround()    (cadr (member :rounding-mode (sb-int:get-floating-point-modes))))

;; (bracket (getround))  returns (:NEGATIVE-INFINITY :POSITIVE-INFINITY)
;;  (let nil(setq one 1.0d0)(setq ten 10.0d0)(bracket(/ one ten))) returns [0.1d0,0.1d0] oddly.
;;  (let nil(setq one 1.0d0)(setq ten 10.0d0)(bracket(/ one ten))) returns (0.09999999999999999d0 0.1d0)
;; I suspect that optimization is just too clever sometimes.
;; (let ((one 1.0d0)(ten 10.0d0))(declare (notinline /))(bracket (/ one ten)))   ;; works here








	
(defmethod ga::two-arg-+ (r (s ri)) ;adding num+interval
  (with-ri s (lo1 hi1 dec1) (widen (+ lo1 r)(+ hi1 r) dec1)))

(defmethod ga::two-arg-+ ((s ri) r)
  (with-ri s (lo1 hi1 dec1) (widen (+ lo1 r)(+ hi1 r) dec1)))


(defmethod ga::two-arg-- ((r ri)(s ri))
  ;; adding 2 intervals, just add their parts.
  ;; to be more precise we should round down for lo, round up for hi.
  ;; can we do this? 
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	   (widen (- lo1 lo2)(- hi1 hi2) (worse dec1 dec2))
	   ))

(defmethod ga::two-arg-- ((r t) (s ri)) ;subtract: num-interval
  (with-ri s (lo1 hi1 dec1)
	   (let((a (- r lo1))(b (- r hi1)))
	     (widen (min a b)(max a b) dec1))))

(defmethod ga::two-arg-- ((s ri) r) ;subtract: interval - num
  (with-ri s (lo1 hi1 dec1)
	   (let((a (-  lo1 r))(b (-  hi1 r)))
	     (widen (min a b)(max a b) dec1))))


#+SBCL  ;; example for how this would be done without widen
(defmethod ga::two-arg-* ((r ri)(s ri))
  ;; multiplying intervals, try all 4, taking min and max.
  ;; to insure validity we round down for lo, round up for hi. 8 total values.
  ;; could do fewer ariths if we do checking, e.g. if intervals are 0<lo<hi.
  (with-ri2 r s (lo1 hi1 dec1 )(lo2 hi2 dec2)
	    (let* ((prodsU 
		    (with-rounding :positive-infinity
		      (list (* lo1 lo2)(* lo1 hi2)(* hi1 lo2)(* hi1 hi2))))
		   (prodsD 
		    (with-rounding :negative-infinity
		      (list (* lo1 lo2)(* lo1 hi2)(* hi1 lo2)(* hi1 hi2))))
		   (sorted (sort (nconc prodsU prodsD) #'<)))
	      (if (some #'nan-pfun sorted) (ri *s-nan* *s-nan* ILL)
		(ri (nth 0 sorted)(nth 7 sorted) (worse dec1 dec2))))))

#-SBCL 
;; This version of two-arg-* multiplies 2 intervals 
;; without trying to set the IEEE rounding mode, just bumping up and down

(defmethod ga::two-arg-* ((r ri)(s ri))
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	    (let ((sorted (sort (list (* lo1 lo2)(* lo1 hi2)(* hi1 lo2)(* hi1 hi2)) #'<)))
	      (if (some #'nan-pfun sorted) (ri *s-nan* *s-nan* ILL)
		(widen (nth 0 sorted)(nth 3 sorted) (worse dec1 dec2))))))

#| documentation, publication
;; Here is the raw Lisp executable code for interval product, without comments.
;; It is not self-contained, but refers to utilities supporting interval objects and code.

(defmethod ga::two-arg-* ((r ri)(s ri))
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	    (let ((sorted (sort (list (* lo1 lo2)(* lo1 hi2)(* hi1 lo2)(* hi1 hi2)) #'<)))
	      (if (some #'nan-pfun sorted) (ri *s-nan* *s-nan* ILL)
		(widen (nth 0 sorted)(nth 3 sorted) (worse dec1 dec2))))))

;;Here is the executable code, but now with comments.

;; This method definition is used by a generic arithmetic function
;; whose name is simply "*". In Lisp, it is used as (* x y) meaning x*y,
;; or (* x y z) meaning x*y*z

;; In reality, multiplication of more than two items is 
;; macro-expanded into two-items at a time, so (* x y z) is more like (* (* x y) z).
;; Actually that is not quite right because once we know that there are exactly
;; two arguments, we call two-arg-* .  Thus  (two-arg-* (two-arg-* x y) z).

;; now what is this generic arithmetic?  The interval package is merely one aspect
;; of this arithmetic.  The other packages include quad-double float arithmetic,
;; polar complex numbers, polynomials, projective rational arithmetic, and others.
;; They sometimes play together nicely, as for example, intervals with endpoints
;; that are quad-doubles, or polynomials whose coefficients are intervals, etc.
;; Sometimes it is not clear how these interactions should behave, as for example,
;; in what domain do we represent zero?

;; The way we incorporated "ri"  (real interval) arithmetic in the generic
;; system is to define how two-arg-* should behave when given two arguments r,s
;; where r is an object in the class ri, and s is an object in the class ri.
;; Other methods can (and are) defined with r and/or s being other numeric types.

;; Thus we define a generic method with the following heading:

(defmethod ga::two-arg-* ((r ri)(s ri))
  
  ;; the next line is a macro defined previously that takes two ri objects
  ;; and two sets of names.  It binds the names, in this case lo1 hi1 dec1 to
  ;; the 3 parts of the ri r, and similarly for s.
  (with-ri2 r s (lo1 hi1 dec1 )(lo2 hi2 dec2)
	    ;; Now that we have the parts picked out, we want to compute the
	    ;; upper and lower bounds for the interval product.  We could check for
	    ;; signs and such, but here we just crudely compute all 4 products,
	    ;; put them in a list, and sort them according to some ordering.
	    ;; It may be worth noting that here we are using the function "*",
	    ;; which is the generic multiplication, so the upper and lower bounds
	    ;; could be any arithmetic types for which * is defined. That includes
	    ;; single or double floats, integers, exact arbitrary precision rationals,
	    ;; or for that matter, intervals again, recursively.  I'm not sure it
	    ;; is sensible to have intervals whose upper and lower bounds are intervals.
	    
	    (let ((sorted (sort (list (* lo1 lo2)(* lo1 hi2)(* hi1 lo2)(* hi1 hi2)) #'<)))
	      ;; The line above binds just a new variable "sorted" to the list,
	      ;; placing the smallest first.  The sort comparison predicate is
	      ;; the generic "<".  If the endpoints are all double-floats, then
	      ;; the comparison will be done with the usual meaning.
	      
	      ;; The next line is something I'm not sure is required or correct,
	      ;; It says that if one or more of the 4 results is not a number,
	      ;; this program should return an illegal (ILL) interval.
	      ;; For purposes of concreteness, a real interval structure is
	      ;; created with lower and upper bounds being single-float NaNs
	      ;; and decoration ILL.  (ILL happens to be a constant 0)
	      (if (some #'nan-pfun sorted)  (ri *s-nan* *s-nan* ILL)
		;; the else clause for that if
		;; picks out the smallest and the largest items from that
		;; 4 element list.  It then bumps the lower one down and
		;; the uppoer one up by one unit in the last place, for
		;; floating-point numbers.  Exact rationals are unchanged by
		;; this bumping up/down.  The last argument to widen is
		;; the worse decoration of the two inputs, a rule that, so
		;; far as I can tell, is agreeable.  If there is another rule,
		;; either we should define worse differently, or use another
		;; decision mechanism to compute the result decoration.
		(widen (nth 0 sorted)(nth 3 sorted) (worse dec1 dec2))))))

;; There are printing programs so that these tests can have printed/ readable results:

(setf xf (widen 1.0d0 2.0d0 dac)) ;; assign a value for xf

(+ xf)          ;; [0.9999999999999999d0,2.0000000000000004d0, /COM]
(+ xf xf)       ;; [1.9999999999999998d0,4.000000000000001d0, /DAC]
(+ xf xf xf)    ;; [2.9999999999999996d0,6.000000000000003d0, /DAC]
(+ xf oo)       ;; [oo,oo, /DAC]
(+ xf -oo)      ;; [-oo,-oo, /DAC]

(setf x (ri 1 2 dac))
(* 3.0 x)         ;; [2.9999998,6.000001, /DAC]
(* x x)           ;; [1,4, /DAC]

(* xf xf)         ;; [0.9999999999999999d0,4.000000000000001d0, /DAC]
|#

(defmethod ga::two-arg-* (r (s ri))
  ;; multiplying num by interval
  (with-ri s (lo1 hi1 dec1)
	   (let ((prods (sort (list (* r lo1)(* r hi1)) #'<)))
	     
	     ;; is this next check required? Correct?
	      (if (some #'nan-pfun prods)(ri *s-nan* *s-nan* ILL)
	      (widen (car prods)(cadr prods) dec1 )))))

(defmethod ga::test (r (s ri))
  ;; multiplying num by interval
  (with-ri s (lo1 hi1 dec1) (+ lo1 hi1)))

(defmethod ga::two-arg-* ((s ri) r) (ga::two-arg-* r s))

;; need to do more stuff for sin cos etc.
;; need to think about rounding up/down
;; can be much more careful with some of these.

(defmethod ga::abs((r ri))(with-ri r (lo hi dec) 
			    (let ((L (abs lo)) (H (abs hi)))
			      (if (<= L H) (ri L H dec)(ri H L dec)))))

;;; we need to figure out scalar  0^ nonpos
(defmethod ga::two-arg-expt (a b)(cl::expt a b))

(defmethod ga::two-arg-expt ((r ri) (p integer))
  (with-ri r (lo hi dec)
	   ;; here are the rules for point function.
	   ;; defined for all R if p>=0
	   ;; defined for all R except R containing 0 if p<0
	   ;; consider cases separately for 
	   ;; p>0 odd, s subset of R
	   ;; p>0 even , a subset of [0,oo] 
	   ;; p=0, [1,1] unless r is 0
	   ;; p<0 odd, subset of R excluding 0
	   ;; p<0 even, subset of (0,oo)
	   (cond 
	    ((> p 0)
		  (if (oddp p) (if (< 0 lo hi) (widen (expt lo p)(expt hi p) dec) 'case1))
		  ;;even
		  (if (< 0 lo hi) (widen (expt lo p)(expt hi p) dec) 'case2))
	    
	    ((eql p 0) 'case3)
	    ((< p 0)(if  (oddp p)
			(if (< 0 lo hi) (widen (expt hi p)(expt lo p) dec) 'case4)
		      
			    			   ;;even
			   'case5)))))

	    
(defmethod ga::two-arg-expt ((r ri) (n real))
  (with-ri r (lo hi dec)
	   (cond 
	    ((< 0 lo hi) (widen (expt lo n)(expt hi n) dec))
	    ((and (< lo 0 hi)
		  (< -1 n 1))
	     (format t "~%interval ~s containing neg to fractional power ~s " r n)
	     (widen 0 (expt hi n) dec))
	  	  
	    (t (error "figure out ~s^(~s)" r n)))))




(defmethod ga::two-arg-expt ((r ri) (n ri))
  ;; allowed: x>0  union  (x=0, y>0)
  (with-ri r (lo hi dec)
	   ;; compute exp(y*log(x)) for real x>0 and all realy, and 0 for x=0 and y>0 else error
	   
	   (error "figure out ~s^(~s)" r n)))
  

#+ignore ;; see later
(defmethod ga::sin ((s ri))
  (with-ri  s (lo hi)
	    (if (>(abs (- hi lo)) pi) (ri -1 1) ; full period
	      (error "please fix program for interval sin ~s" s))))

(defmethod cos ((s ri))
  (with-ri  s (lo hi)
	    (if (>(abs (- hi lo)) pi) (ri -1 1) ; full period
	      (error "please fix program for interval cos ~s" s))))

;; not very careful log function. Need to assure accuracy of built-in log
;;  we depend on assumption that log is good to 1/2 ULP.
(defmethod log ((s ri))
  (with-ri  s (lo hi dec)	    
	    (let ((L (cond ((<= lo 0)(setf dec DEF)(- Inf))
			   (t (cl::log lo))))
		     
		  (H (cond ((<= hi 0)(setf dec EMP) NaN)
			   (t (cl::log hi)))))
	      (widen L H dec))))

;; must catch overflow. this one doesn't
#+ignore
(defmethod ga::exp ((s ri))
  (with-ri  s (lo hi dec)	    
	    (widen (cl::exp lo)(cl::exp hi) dec)))

;; this catches overflow and returns Inf.
(defmethod ga::exp ((s ri))
  (with-ri  s (lo hi dec)	    
	    (widen (expwinf lo)(expwinf hi) dec)))


(defun expwinf(h)  ;; exp function with infinity and NaN too.
  (handler-case (cl::exp h)
    (floating-point-overflow () Inf)
    (error () NaN)))

(defun divwnan(g h)  ;; division with NaN for 0/0, 1.0, -1/0
  (handler-case (/ g h)
    (division-by-zero (z) 
      (cond ((cl::= g 0)NaN)((cl::< g 0) (- Inf))(t Inf)))))

(defmethod ga::two-arg-/ ((r ri)(s ri))
  ;; dividing intervals, try all 4, taking min and max.
  ;; for floats we should round down for lo, round up for hi.
  ;; could be done faster, e.g. if intervals are 0<lo<hi.
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)
	    (if (<= lo2 0 hi2)		; divisor contains zero 
		(progn
		  (format t "~%warning: division by interval containing zero ~s" s)
		  (ri *dn-inf* *d-inf* DEF)) ;; what decoration??
	      (let ((quos (sort (list (/ lo1 lo2)(/ lo1 hi2)(/ hi1 lo2)(/ hi1 hi2)) #'<)))
		;; check for NaNs?
		(widen (car quos)(fourth quos) (worse dec1 dec2))))))


(defmethod ga::two-arg-/ ((r ri)(s t))  ; scalar 2nd
  (with-ri r (lo1 hi1 dec)
	    (if (= s 0)		; divisor is zero
		(progn
		  (format t "~%warning: division by  ~s" s)
		  (ri *dn-inf* *d-inf* DEF)) ;; what decoration??
	      (let ((quos (sort (list (/ lo1 s)(/ hi1 s)) #'<)))
		;; check for NaNs?
		(widen (car quos)(cadr quos) dec)))))

(defmethod ga::two-arg-/ ((r t)(s ri))  ;scalar 1st arg
  (with-ri  s (lo2 hi2 dec)
	    (if (<= lo2 0 hi2)		; divisor contains zero 
		(progn
		  (format t "~%warning: division by interval containing zero ~s" s)
		  (ri *dn-inf* *d-inf* DEF)) ;; what decoration??
	      (let ((quos (sort (list (/ r lo2)(/ r hi2)) #'<)))
		;; check for NaNs?
		(widen (car quos)(cadr quos) dec)))))



;; how to refine an interval..
;; find the minimum and maximum of f on the interval. Or approximate them.


;; for example,
#| 
   
   This is interesting for functions that have local max and min,
   say a polynomial which, if naively evaluated with intervals over
   a region with local extrema, will evaluate to an interval that
   is larger than necessary.  These routines will sometimes find
   a tighter interval by subdivision.
   e.g. 
     (defun test(x)(* x (+ x 4)(+ x -4))) ;;  x*(x+4)*(x-4)

 (test (ri -5.0d0 5.0d0)) --> [-405.00000000000017d0,405.00000000000017d0]  regular arithm.
 (maxi #'test (ri -5.0d0 5.0d0) 5)  --> 45.00000000000002d0  maximum on interval
 (mini #'test (ri -5.0d0 5.0d0) 5) --> -45.000000000000014d0 minimum on interval

   Actually a tight bound is [-45,45]
   

|#

(defmethod mini (f (r ri) (c fixnum))
  (with-ri r (lo hi)
	   (mini2 f lo hi (funcall f r) c)))

(defun mini2(f a b val count)
  (if (<= count 0) (ri-lo val)
  (let*
      ((m (/(+ a b) 2))
       (f1 (funcall f (ri a m)))
       (f2 (funcall f (ri m b)))
       (mf1 (ri-lo f1))
       (mf2 (ri-lo f2))
       (ans 0))
    (cond ((< mf1 mf2)
	   (setf ans (mini2 f a m f1 (1- count)))
	   (if (< ans mf2) ans (min ans (mini2 f m b f2 (1- count)))))
	  (t
	   (setf ans (mini2 f  m b f2 (1- count)))
	   (if (< ans mf1) ans (min ans (mini2 f a m f1 (1- count)))))))))

	   
;;; short version of maxi.
#+ignore
(defmethod maxi(f (r ri) (c fixnum))
  (with-ri r (lo hi)
	  (- (mini2 #'(lambda(r)(- (funcall f r)))
		  lo hi (funcall f r) c))))
       

;;; longer version, saves some function calls and negations.
(defmethod maxi(f (r ri) (c fixnum))
  (with-ri r (lo hi dec)
	   (maxi2 f lo hi (funcall f r) c)))

(defun maxi2(f a b val count)
  (if (<= count 0) (ri-hi val)
  (let*
      ((m (/(+ a b) 2))
       (f1 (funcall f (ri a m)))
       (f2 (funcall f (ri m b)))
       (mf1 (ri-hi f1))
       (mf2 (ri-hi f2))
       (ans 0))
    
    (cond ((> mf1 mf2)
	   (setf ans (maxi2 f a m f1 (1- count)))
	   (if (> ans mf2) ans (max ans (maxi2 f m b f2 (1- count)))))
	  (t
	   (setf ans (maxi2 f  m b f2 (1- count)))
	   (if (> ans mf1) ans (max ans (mini2 f a m f1 (1- count)))))))))

;; uses memoizing, in case f is hard to evaluate.
(defmethod refine-mem(f (r ri) (c fixnum))
  (labels
      ((lo-hi(r)(setf r (car r))(ma::ucons (ri-lo r)(ri-hi r)))
       (memoize(fn-name &key (key #'lo-hi) (test #'eq))
	 (amlparser::clear-memoize fn-name)
	 (setf (symbol-function fn-name)
	         (amlparser::memo (symbol-function fn-name)
              :name fn-name :key key :test test))))
    (memoize f :key #'lo-hi :test #'eq)
    (ri (mini f r c)(maxi f r c))))

(defmethod refine(f (r ri) (c fixnum)) ;; don't memoize.  May be faster, often.
  
  ;; should check that r is a proper interval,
  ;; here's one way.
   (let* ((lo (ri-lo r))(hi (ri-hi r))(m (/ (+ lo hi) 2)))
     (unless (< lo m hi) (format t "~%cannot refine on ~s"ri) (funcall r ri))

    (ri (mini f r c)(maxi f r c))))


(defun badguy(x)  ;; return true for inf, -inf, nan.  single or double.
  #+allegro(excl::exceptional-floating-point-number-p x)
  #+sbcl (or (sb-vm::float-nan-p x) (sb-vm::float-infinity-p x))
  #+gcld (or (float-nan-p x) (float-inf-p x))
  )

(defmethod left ((r ri))(ri-lo r))
(defmethod left ((r t)) r)
(defmethod right((r ri)) (ri-hi r))
(defmethod right((r t)) r)

(defconstant empty-ri (ri *d-nan* *d-nan* EMP))

(defconstant piby2 (cl::/ cl::pi 2))

(defmethod intsin((z ri))
"real interval sin of an interval of machine numbers."
;; result endpoints are same precision as inputs,  if float. If inputs
;; are rational, the result will be double on most Lisps. If 
;; we note that extrema -1 or 1 are reached, that result endpoint will be an integer.
 (with-ri z (low hi dec)
   (cond 
    ((or (badguy low)(badguy hi)(> low hi)) *m1to1*) ; check for infinity, Nan, out-of order.
    ;; we might also check if low and high are too large for accuracy.
    ((eql low hi)
     (let((ans (sin low)) 
	  (ri (ri (bd ans)(bu ans))))
       ))
    
    ((>= (- hi low) #.(cl::* 2 pi)) *m1to1*)  ; [-1,1] if range > 2 pi
    (t(let* ((u (sin (if (rationalp hi)(coerce hi *preferred-float*) hi)))
	     (v (sin (if (rationalp low)(coerce low *preferred-float*) low)))
	     (minval (bd (min u v)))
	     (maxval (bu (max u v)))
	     (h (floor hi piby2)))
	;; check if sin(z) hits -1 or 1 in the interval. 
	(do 
	 ((k  (ceiling low piby2) (1+ k)))
	 ((> k h)(ri minval maxval))
	 (case (mod k 4)
	       (1 (setf maxval 1))
	       (3 (setf minval -1)))))))))

;; here are tests: (intsin (ri 0 pi))
;;                 (intsin (ri pi (* 2 pi)))
;;                 (intsin (ri (- pi) pi))
;;                 (intsin (ri -1.0 1.0))
;;                 (intsin (ri -1.0d0 1.0d0))


(defmethod ga::sin((z ri)) (intsin z))

;; to use this definition of sin, you must do (in-package :interval)

(defmethod bu ((k double-float)) (if (cl::> k 0)(cl::* k #.(cl::+ 1 double-float-epsilon))
				   (cl::* k #.(cl::- 1 double-float-epsilon))))

(defmethod bu ((k single-float)) (if (> k 0)(* k #.(cl::+ 1 single-float-epsilon))
				   (* k #.(cl::- 1 single-float-epsilon))))
;(defmethod bu ((k (eql 0))) 0) ;exactly 0 stays zero same as rationals
(defmethod bu ((k ratio)) k)
(defmethod bu ((k integer)) k)
(defmethod bu ((k (eql 0.0))) least-positive-normalized-single-float)
(defmethod bu ((k (eql 0.0d0)))least-positive-normalized-double-float)
(defmethod bu ((k (eql *dn-inf*))) most-negative-double-float) ;;
(defmethod bu ((k (eql *sn-inf*))) most-negative-single-float) ;;

(defmethod bd ((k (eql 0.0))) least-negative-normalized-single-float)
(defmethod bd ((k (eql 0.0d0))) least-negative-normalized-double-float)

;; do we need cl::?
(defmethod bd ((k double-float)) (if (cl::< k 0)(cl::* k #.(cl::+ 1 double-float-epsilon))
				   (cl::* k #.(cl::- 1 double-float-epsilon))))

(defmethod bd ((k single-float)) (if (< k 0)(* k #.(+ 1 single-float-epsilon))
				   (* k #.(- 1 single-float-epsilon))))
(defmethod bd ((k ratio)) k)
(defmethod bd ((k integer)) k)

(defmethod bd ((k (eql *d-inf*))) most-positive-double-float) ;;
(defmethod bd ((k (eql *s-inf*))) most-positive-single-float) ;;

(defun nextup(x)(bu x))  ;; IEEE names
(defun nextdown(x)(bd x))

(defmethod coerce-to((r ri) (h t))
  ;; 2nd argument is coercion target.  E.g. ratio.
  ;; 1st argument is a real interval
  
  (with-ri r (lo hi dec)
	   (cond 
	    ((eq h 'ratio) (ri (cl::rational lo) (cl::rational hi)  dec))
	    ;; maybe check for request for MPFR or quad-double...
	    ;; this coercion is not necessarily an enclosure
	    (t   (ri (coerce lo h) (coerce hi h)  dec))
	    ;; or do we want to widen??
	    ;;  (t   (widen (coerce lo h) (coerce hi h)  dec))
	    )))


;;(defun widen (a b decor) (ri (bd a)(bu b) decor))   defined as macro


;;; these methods all need to be examined for nan and inf  and empty etc args.
(defmethod includes-ri ((r ri)(s ri)) ;; r is inside s
  (with-ri2 r s (lo1 hi1)(lo2 hi2)
	    (<= lo1 lo2 hi2 hi1)))

(defmethod intersect-ri ((r ri)(s ri)) ;; 
  ;; if the intersection is empty, what interval should we return??
  (with-ri2 r s (lo1 hi1 dec1)(lo2 hi2 dec2)  ;; what to do
	    
	    (cond
	    ;; case 1 [lo1---hi1]
	    ;;            [lo2 ---hi2]
	    ((<= lo1 lo2 hi1 hi2) (ri lo2 hi1))

	    ;; case 2 [lo2---hi2]
	    ;;            [lo1 ---hi1]
	    ((<= lo2 lo1 hi2 hi1) (ri lo1 hi2))

	    ;; case 3,4 [lo2------------hi2]
	    ;;             [lo1 ---hi1]
	    ((<= lo2 lo1 hi1 hi2) r)
	    ((<= lo1 lo2 hi2 hi1) s)

	    ;; case 5,6 [lo1---hi1]
	    ;;                     [lo2 ---hi2]
	    ((or(< hi1 lo2)
		(< hi2 lo1))
	      (ri NaN NaN EMP))	    )))

(defmethod ga::two-arg-= ((r ri)(s ri)) ;; both intervals are points, equal
    (with-ri2 r s (lo1 hi1)(lo2 hi2) (= lo1 lo2 hi1 hi2)))
  
  
;; possibly-equal is ok 
(defmethod possibly-= ((r ri)(s ri)) ;; 
  ;; if the intersection is empty, not equal
  (intersect-ri r s))

(defmethod possibly-= ((r ri)(s t)) ;; 
  (element-ri s r))

(defmethod possibly-= ((s t)(r ri)) ;; 
  (element-ri s r))
(defmethod element-ri ((elt t)(r ri))
  (<= (left r) elt (right r)))

(defmethod possibly-< ((r ri)(s ri)) ;; 
  (or  (intersect-ri r s) (< r s)))

(defmethod possibly-> ((r ri)(s ri)) ;; 
  (or  (intersect-ri r s) (> r s)))

(defmethod ga::two-arg-min((x ri)(y t)) (if (ga::< x y) x y)) 
(defmethod ga::two-arg-min((x t)(y ri)) (if (ga::< x y) x y)) 
(defmethod ga::two-arg-min((x ri)(y ri)) (if (ga::< x y) x y)) 
(defmethod ga::two-arg-max((x ri)(y t)) (if (ga::> x y) x y)) 
(defmethod ga::two-arg-max((x t)(y ri)) (if (ga::> x y) x y)) 
(defmethod ga::two-arg-max((x ri)(y ri)) (if (ga::> x y) x y)) 

(defmethod ga::two-arg-< ((r ri)(s ri))
  (< (ri-hi r) (ri-lo s)))

(defmethod ga::two-arg-< ((r ri) s)  ;; always less
  (< (ri-hi r) s))
(defmethod ga::two-arg-< (s (r ri))  ;; always less
  (< s (ri-lo r)))

(defmethod ga::two-arg-> ((r ri)(s ri))  ;; always greater
  (> (ri-lo r) (ri-hi s)))
(defmethod ga::two-arg-> ((r ri) s)  ;; always greater
  (> (ri-lo r) s))
(defmethod ga::two-arg-> ( s (r ri ))  ;; always greater
  (> s (ri-hi r)))


;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; IEEE specific functions

;;(defun text2interval(s)  takes a string!) ;; probably not necessary in Lisp.

(defun nums2interval(l u) (ri l u))
(defun bareempty()(ri *s-nan* *s-nan* EMP)) ;; maybe ?
;;(defun bareempty()(ri *sn-inf* *s-inf* DAC)) ;; DAC?? maybe ?

;; guessing what the empty interval representation will be.
(defmethod isEmpty((r ri))  ;returns t or nil
  (<= (ri-decor r)EMP))

#+ignore
(defmethod isEmpty((r ri))   ; the version returning 1 or 0 
  (if (<=(h (ri-decor r))EMP) 1 0))

;; if <= returned 1 or 0, rather than t or nil, we could write  (<=(ri-decor r)EMP)
  

;; This next definition depends on double-inf and single-inf being numerically equal.
;; I don't know if this is an axiom or a bug.

;; It also returns  T or nil, the convention in Lisp, rather than 1 and 0.

;; This could easily be changed but my first impression is this would
;; make many conditional tests a little longer and clumsier.  Instead
;; of (if test R S) write (if (eq test 1) R S)

;; Instead of Lisp's 

;;  (and test1 test2) 

;; one could write something like this

;;  (if (and (eq test1 1)(eq test2 1)) 1 0)

;; Sometimes the logic can be done with arithmetic,  e.g. this might be
;; written, if true=1, false=0, as
;;    (* test1 test2)
;; and sometimes this is neater.


(defmethod isEntire((r ri))(with-ri r (lo hi dec)
				    (and (inf-p lo)(inf-p hi) (< lo hi))))

(defmethod isEqual((A ri)(B ri))
  ;; if isEmpty returns T or NIL
  (cond ((isEmpty A)
	 (if (isEmpty B) t nil)) ;; both empty, return t. one empty, false.
	((isEmpty B) nil)
	(t  (with-ri2 
		A B (loA hiA decA)(loB hiB decB)
		(= loA loB)(= hiA hiB)))))

#+ignore
(defmethod isEqual((A ri)(B ri))
  ;;; if isEmpty returns 1 or 0.  This turns out to be brief
  
  (case (+(isEmpty A)(isEmpty B))   ;; addition is used like logical OR
    (0 (with-ri2			;neither is empty. do some arithmetic
		A B (loA hiA decA)(loB hiB decB)
		(= loA loB)(= hiA hiB)))
    (1 0)				;one of them is empty
    (2 0))				;both are empty
  )

;; containedIn less precedes isInterior strictlyLess strictlyPrecedes areDisjoint

(defmethod isInterior(A B)
  ;; if A is empty, then it isInterior to B
  ;; unless  B is also empty in which case it is not.
  (cond ((isEmpty A)(if (isEmpty B) nil t))
	(t
	 (with-ri2			;neither is empty. do some arithmetic
	     A B (loA hiA decA)(loB hiB decB)
	     ;; we assume that loA<=hiA if the infinity stuff is to work ok.
	     (and (or (< loA loB) 
		      (and (inf-p loA)(= loA loB) )) ; loA<loB or equally infinite + or -
		  (or (< hiA hiB) 
		      (and (inf-p hiB)(= hiA hiB)))))))) ; hA<loB or equally infinite + or -.
		  

;;;IEE 1788 chapter 2 section 9.6.3, table 1 
;; requires neg add sub mul div recip sqrt fma,
;; sqr pown pow exp exp2 exp10 log lo2 log10
;; sin cos tan asin acos atan atan2 sinh cosh tanh asinh acosh atan
;; sign ceil floor trunc
;; roundTiesToEven roundTiesToAway
;; abs min max
;; case

;; most pretty much obvious definitions.
;; except fma = fused multiply add, f(x,y,z):= x*y+z
;; pown is x^n
;;roundTiesToEven(x); roundTiesToAway(x)
;; are the nearest integer to x, with ties rounded to the even integer 
;; or away from zero respectively.
;; case .. see document; case(c,g,h) is like if empty(c) then EMP else if c<0 then g else 
;; if c>0 h  else convexHull(g,h).

#|
The (interval) hull of an arbitrary subset s of Rn, written hull(s), is the tightest
member of IRn that contains s.

When f is a binary operator X written in infix notation, this gives the usual definition 
of its natural interval extension as

x X y = hull(f x X y j x 2 x, y 2 y, and x X y is defined g):

Example. With these definitions, the relevant natural interval extensions satisfy
sqrt ([1, 4]) = [0, 2] and sqrt([-2,-1]) = empty set.

|#


(defmethod real-sqrt((r real))(cl::sqrt r))

(defmethod real-sqrt((c complex))(cl::sqrt(realpart c))) ;; perhaps.

(defmethod ga::sqrt((r ri)) ;;this is usual forward sqrt, dropping off
  ;; negative args
  (with-ri r (lo hi dec)
	   (if (rationalp hi)(setf hi(coerce hi *preferred-float*)))
	   (if (rationalp lo)(setf lo (coerce lo *preferred-float*)))
	   (cond ((<= 0 lo hi)(widen (sqrt lo)(sqrt hi) dec))
		 ((< hi 0)(ri NaN NaN EMP))
		 ;; (< lo 0 hi), ignore  (< x 0) as not in sqrt domain.
		 (t (ri 0 (bu (sqrt hi)) DEF)))))


#|
Reverse-mode Interval functions...
unary:  given psi(X) , 
derive psiRev(c,X) which encloses {x in X such that psi(x) is defined and in c}
binary: given psi(X,Y), there are two reverse modes, with respect to first or second arg.

required reverse functions
unary: sqrtRev recipRev absRev pownRev sinRev cosRev tanRev coshRev
binary: mulRev divRev1 divRev2 powRev1 powRev2 atan2Rev1 atanRev2

Additional Non-arithmetic function
inf(x)  lower bound, infinity if empty
sup(x) upper bound, minus infinity if empty
mid  "no value if x empty or unbounded"
wid  "no value if x is empty?"
mag  sup abs(x)
mig  inf abs(x)
|#
;;; acl features
;;(= excl::*nan-double* excl::*nan-double* ) is false, correct IEEE 754


#| a Maxima interpreter for intervals |#

(defpackage :maxima)
(in-package :ri)			; real interval

(defun maxima::$ieval(expr)
  (catch :ieval-fail (ieval expr)
	 ;; by the time $ieval is called, expr is meval'd. (maxima::meval expr)
	 ))
(defvar maxima::$intervalwidth (expt 2 -53))

;;(setf  maxima::$intervalwidth (expt 2.0d0 -40))

(defun maxima::$interval (e1 &optional (e2 e1)) ;  interval(x) is same as interval(x,x).
  (cond ((and (eq e1 e2) (eq e2 'maxima::$%pi))
	 (let ((z (apple-pint (ceiling(- (/ (cl::log maxima::$intervalwidth) #.(cl::log 2.0)))))))
	   (ri::ri (coerce (ri::ri-lo z) (type-of maxima::$intervalwidth))
		   (coerce (ri::ri-hi z) (type-of maxima::$intervalwidth)) DAC)))
	(t		   
	  (ri::ri (toclnum e1)(toclnum e2)))))
      
(defun maxima::$widen (e1 &optional (e2 e1));  interval(x) is same as interval(x,x).
  (ri::widen (toclnum e1)(toclnum e2) DAC))

(defun toclnum(e)
  ;; handle numbers that are ((rat) 1 2) e.g.
  ;; maybe this should handle bigfloat or complex somehow
  (cond ((and (listp e)(eq (caar e) 'maxima::rat))
	 (let ((v (/ (cadr e)(caddr e)))) ; make a CL ratio
	   v))
	;; maybe check for inf or nan here
	((eq e 'maxima::$inf) *d-inf*)
	((eq e 'maxima::$mminf) *dn-inf*)
	;; let nan through?
	((numberp e) e)
	(t (maxima::merror "illegal endpoint for interval; ~a"  (coerce (maxima::strgrind e) 'string)))))

(defun ievalfail(e) 
  (throw :ieval-fail (format nil  "IEVAL cannot evaluate to an interval:  ~a" 
			     (coerce (maxima::strgrind e) 'string))))

(defun ieval(e)
  (cond ((realp e) (widen e e DAC))	;3.0 -> [3-eps,3+eps]
	((ri-p e) e)			; a real interval
	((atom e) 
	 (ievalfail e))
	((eq (caar e) 'maxima::rat)(ieval(toclnum e)))
	(t (case 
	       (caar e) 
	     (maxima::MPLUS 
	      (cond ((null (cdr e)) 0)
		    ((null (cddr e))(ieval (cadr e)))
		    (t  (+ (ieval (cadr e)) ;this + is a real-interval +
			   (ieval (cons (car e) (cddr e)))))))
	     (maxima::MTIMES
	      (cond ((null (cdr e)) 0)
		    ((null (cddr e))(ieval (cadr e)))
		    (t  (* (ieval (cadr e)) ; this * is a real-interval *
			   (ieval (cons (car e) (cddr e)))))))
	     (maxima::MEXPT
	      (if (integerp (caddr e))(expt (ieval (cadr e))(caddr e)) ;integer power
		(expt (ieval (cadr e))(caddr e)))) ; general case
	   
	     (otherwise
	      ;; look on property list of (car e) 
	      ;; to see if it has an ieval property. eg.
	      
	      (if (setf fn (get (caar e) 
				'ri::ieval))
		  ;; (funcall fn (cadr e)) ;; functions of one argument; should ieval be called on args??
		  (apply fn (mapcar #'ieval (cdr e)))

		(ievalfail e))))   )))


(setf (get 'maxima::$includes 'ieval) #'includes-ri)
(setf (get 'maxima::$intersects 'ieval) #'intersect-ri)

(setf (get 'maxima::$inf 'ieval) #'(lambda(x)(ri-lo x)))
;;simpler...
(defmethod maxima::$inf((r ri))(ri-lo r))
(defmethod maxima::$sup((r ri))(ri-hi r))
(defmethod maxima::$isinterior((s t)(r ri))
  (setf s (toclnum s))
  (and (>= s (ri-lo r))(<= s(ri-hi r))))

(defmethod maxima::$isinterior((A ri)(B ri))
  	 (with-ri2		
	     A B (loA hiA decA)(loB hiB decB)
  (and (>= loA loB)(<= hiA hiB))))

(setf (get 'maxima::$sup 'ieval) #'(lambda(x)(ri-hi x)))

(setf (get 'maxima::%sin 'ieval) #'intsin) ;; etc etc for log, exp, power, 

(defun maxima::$RealInterval(a b)(ri a b DAC)) ;; constructor
(defun maxima::$RI(a b)(ri a b DAC)) ;; constructor



#|

	   #+ignore ;; create using $RealInterval
	   (maxima::MLIST
		     ;; make a real interval, a structure of type ri
		     ;; check it is a list of 2 items
		     ;; both numbers, in order, 
		     (let ((a (second e))(b (third e)))
		       (if (and (realp a)
				(realp b)  ;; optional? (<= a b)
				(null(cdddr e)))
			   (widen-ri (cadr e)(caddr e))
			 (error "can't convert ~s to interval"))))
	   
	   #+ignore
	   (maxima::$RealInterval  ;; this would already be evaluated away..
		     ;; make a real interval, a structure of type ri
		     ;; check it is a list of 2 items
		     ;; both numbers, in order, 
		     (let ((a (second e))(b (third e)))
		       (if (and (realp a)
				(realp b)  ;; optional? (<= a b)
				(null(cdddr e)))
			   (ri (cadr e)(caddr e))
			 (error "can't convert ~s to interval"))))
			 |#

#|regression tests

(widen 1 2 com)              ;; [1,2, /com]
(widen 1.0 2.0 com)          ;; [0.99999994,2.0000002, /COM]
(widen 1.0d0 2.0d0 com)      ;; [0.9999999999999999d0,2.0000000000000004d0, /COM]
(widen -1.0 1.0 com)         ;; [-1.0000001,1.0000001, /COM]
(widen 0.0d0 0.0d0 com)      ;; [-2.2250738585072014d-308,2.2250738585072014d-308, /COM]
(widen 0.0 0.0 com)          ;; [-1.1754944e-38,1.1754944e-38, /COM]

(widen *d-nan* *d-nan* ill)  ;; [NaN,NaN, /ILL]
(widen *dn-inf* *d-inf* dac) ;;[-oo,oo, /DAC]
(widen *dn-inf* *dn-inf* com) ;; [-oo,-1.7976931348623157d+308, /COM]

(setf xf (widen 1.0d0 2.0d0 com))
(+ xf)
(+ xf xf)       ;; [1.9999999999999998d0,4.000000000000001d0, /DAC]
(+ xf xf xf)    ;; [2.9999999999999996d0,6.000000000000003d0, /DAC]
(+ xf oo)       ;; [oo,oo, /DAC]
(+ xf -oo)      ;; [-oo,-oo, /DAC]

(setf x (ri 1 2 dac))
(* 3.0 x)         ;; [2.9999998,6.000001, /DAC]
(* x x)           ;; [1,4, /DAC]

(* xf xf)         ;; [0.9999999999999999d0,4.000000000000001d0, /DAC]





|#

;;(sinis x x x 2 5)  ;; 2 , 4, ... 


;; compute a lower and upper bound on sin(x) based on
;; the series expansion of degree k or k+2, bracketing.
;; if k is too large, the bracketing property will be
;; lost for float x because the correction will be too small, and
;; both upper and lower limits willbe the same point.
;; It works for x rational however.
;; This program does not do range reduction and so
;; is kind of klunky slow for large magnitude args.

#|
(defun s(x k)(sinis x x x 2 k))

(defun sinis(sum x term n lim)  ;; sin of a scalar, inf sup
  (let ((term (/(* -1 term x x)
		(* n (1+ n)))))
    (if (>= n lim) 
	(let ((nextsum (+ sum term)))
	  (list (max -1 (min sum nextsum))
		(min 1 (max sum nextsum))))
      (sinis (+ sum term) x term (+ n 2) lim))))

(defun se(x err)(siniserr x x x 2 err)) ;; compute sin_inf and sin_sup separated by < err

(defun sinratint(x)
  ;; crappy program:
  ;; this can just compute sin(interval(0.5,0.6)) by series but it is lousy,
  ;; no surprise.  Better to compute interval around sin(0.5) and around sin(0.6).
  
  (let ((h (siniserr x x x 2 maxima::$intervalwidth )))
    (if (ri-p (car h))
	(ri (cl::min (ri-lo (car h))(ri-lo (cadr h)))
	    (cl::max (ri-hi (car h))(ri-hi (cadr h))))
      (ri (car h)(cadr h)))))

(defun siniserr(sum x term n err)  ;; sin inf sup, stop when gap between 2 sums is <err
  (let ((term (/(* -1 term x x)
		(* n (1+ n)))))
    (if (< (abs term) err) 
	(let ((nextsum (+ sum term)))

	  #+ignore ;; use for ri argument.  bad idea.  but why is ga::max not generic?
	  (list (ga::max -1 (ga::min sum nextsum))  ;; need min and max on intervals
		(ga::min 1 (ga::max sum nextsum)))
	  

	  (list (max -1 (min sum nextsum))  ;; need min and max on intervals
		(min 1 (max sum nextsum)))
	  )
      (siniserr (+ sum term) x term (+ n 2) err))))



;;; this above doesnt work because
;;; (se 1/2 (* 2 double-float-epsilon))
;;; gives two numbers which each round to the same double float,
;;; (20543323773249479/42849873690624000 3493762546471/7287393484800)
;;; (mapcar #'(lambda(r)(* r 1.0d0))*)
;;; (0.479425538604203d0 0.479425538604203d0)
;;; so that's not good.

;;; what we need to do is :

#| given exact rational x compute  lo <=FUN(x) <=hi where |hi-lo| <= 1 ulp
and lo, hi are both some float format F, e.g. F is double.  Let us assume
that we don't encounter =inf or NaN for the moment.

Among the consequences of our requirement is that
either lo or hi is
the closest F number to r:=FUN(x) and thus one of them
is computed by a round-to-nearest default, if r
is guaranteed to be good to <= 0.5 ulp. As some routines are.
But we don't know if r==lo or r==hi.  If we knew that r==lo, then
hi=nextup(lo) and we are done.  Similarly for r==hi, lo:=nextdown(hi).

Furthermore, if we know that r:=FUN() has zero error, as, for 
example sqrt(16.0), we could set lo:=hi:=4.0.  

Note that we cannot do this by finding a rational 
approximation say sx to the transcendental value of sin(x) and
bumping it down and bumping up to two bounds.
The width of that interval is 2ULP not 1ULP.

One way to do this (I think) is start with an algorithm that 
sums exactly the partial rational sums of alternating-sign terms
of a convergent series.  We know that the last term omitted bounds
the error. say that we are left with S+nxt  where 0<nxt<=1ulp
then  S is a lower bound and nextup(S) is upper bound.
or if -1ulp<=nxt<=0,  we have S is upper and nextdown(S) is lower.

|# 
;; sin(x) given 2 arguments x eps , finds a 1 ulp
(defmethod sinuo((x double-float))
  (sinunderoverd x x x 2))
(defmethod sinuo((x real))
  (sinunderoverd x x x 2))

(defmethod sinuo((x single-float))
  (sinunderovers x x x 2))

(defun sinunderoverd(sum x term n)  ;; sin inf sup, stop when gap between 2 sums is <err and next term>0
  (let ((term (/(* -1 term x x)
		(* n (1+ n)))))
    (if (< (abs term) (* double-float-epsilon (abs sum) )) ;; it's close
	(let ((nextsum (+ sum term)))
	  (if (> nextsum sum)		; nextsum is hi
	      (list  (max -1 (ri::bd (setf nextsum (* 1.0d0 nextsum))))
		     nextsum)
	    (list  (setf nextsum (* 1.0d0 nextsum))
		   (min 1 (ri::bu nextsum)))))

      (sinunderover (+ sum term) x term (+ n 2)))))
;; single version
(defun sinunderovers(sum x term n)  ;; sin inf sup single float.
  (let ((term (/(* -1 term x x)
		(* n (1+ n)))))
    (if (< (abs term) (* single-float-epsilon (abs sum) )) ;; it's close
	(let ((nextsum (+ sum term)))
	  (if (> nextsum sum)		; nextsum is hi
	      (list  (max -1 (ri::bd (setf nextsum (* 1.0 nextsum))))
		     nextsum)
	    (list  (setf nextsum (* 1.0 nextsum))
		   (min 1 (ri::bu nextsum)))))

      (sinunderovers (+ sum term) x term (+ n 2)))))

;;For an interval sin ([a,b]) compute se(a), se(b), toss in 1, -1 as needed. Find min and max.
|#

;; for mini and maxi enhancement, we might want to take a program that
;; computes f(x) and construct a program that computes f(x) and f'(x).
;; this is done in the generic arithmetic package dcomp.  the program
;; below is modified from dc in dcomp.lisp instead of (defun test(x)(*
;; x (+ x 4)(+ x -4))) ;; x*(x+4)*(x-4) type (ri::defdiff test2 (x)(*
;; x (+ x 4)(+ x -4)))



(defmacro ri::defdiff (name arglist body) ;; put the pieces together
  (progn
    (setf (get name 'defdiff) name)
  (let ((r (ri::dc-nodecs body (car arglist) (cdr arglist)))) ;; returns a body thatreturns 2 valus.
    `(defun  ,name , (cadr r) ,@(cddr r)))))


(defun ri::dc-nodecs (f x &optional (otherargs nil)) 
  ;; produce a program, p(v) ready to go into the compiler to
  ;; compute f(v), f'(v), returning result as a structure, a df
  (let ((user::*difprog* nil)
	(user::*bindings* nil)
	(user::*lvkd* (list '(pi . 0))) ; for example
	(user::*subexp* (make-hash-table :test #'equal))
        (*v* (gentemp "g")))
    (declare (special *v*))
    (multiple-value-bind
	(val dif)
	(user::dcomp1 f x *v*)
      (user::emit `(df ,val ,dif))
      `(lambda (,*v* ,@otherargs)
	 	 ,(format nil "~s wrt ~s" f x)
	 (let ,(mapcar #'(lambda (r)(list r 0d0)) user::*bindings*)
	   ,@(nreverse user::*difprog*))))))


;;; some stuff dealing with pi
;;;
(setf  *pi333* 54971606468298087752956649260810266548667957980587204204356455828289234687359429673775107185983813579)
;; if you want n bits of pi as a rational number, try  (apple-pi n).  n< 333.  

(defun apple-pi(n) (if (< n 333) (/ (ash *pi333* (- n 333)) (expt 2 n))
		     (error "Only 333 bits of pi are stored at the moment")))
(defun apple-pint(n)(if (< n 333)
			(let ((v  (ash *pi333* (- n 333)))
			   (d (expt 2 n)))
			  (ri (/ v d) (/ (1+ v) d)))
		      (error "Only 333 bits of pi are stored at the moment")))
		      
;; the program below returns a double-float interval, not tight unless n=50
;; not particularly useful.

#+ignore 
(defun apple-pintf(n) (let ((v  (* 1.0d0 (ash *pi333* (- n 333))))
			   (d (expt 2 n)))
		       (ri (/ v d) (/ (1+ v) d))))




#|
Here's the design for interval arithmetic for Maxima.
(and description of the implemented interface so far)

First, an Executive Summary for Interval Arithmetic  (IA)

IA is a system where that each ordinary realscalar arithmetic
operation is replaced by an interval computation such that each 
original number and result is represented by a validated enclosure of that
number.  This produces valid answers even in the face of roundoff
(etc.), though perhaps the result intervals are larger than one
would like.  The skill in implementing and using IA is to keep the
result intervals as tight as possible.

Recall that with ordinary machine arithmetic like x+y->z, we know that
for floating-point x and y, the true mathematical sum z may differ
from the computed sum because of roundoff, overflow etc.

With IA, X, Y,and Z are segments of the real line, with lower and
upper bounds exactly representable. By being careful and slightly
pessimistic, we can construct an enclosure Z such that for any
possible value x in X and y in Y, then Z contains the true
mathematical sum x+y. 

For Maxima:

Under the covers there is a structure that stores intervals as
a pair: lower and upper bounds.  Also some other material perhaps
that may come up in some standardization now in process via
an IEEE committee is stored.  This system requires only Common Lisp, and
so the Maxima version of IA is really a front-end access for the
IEEE reference-implementation-in-progress interval programs.

The principal interfaces:

interval(a,b) constructs an interval from a to b, where the endpoints
are the particular machine-representable numbers a, b.  In single or double
precision, or exact integer or exact rational form. 
(Not yet bigfloats.) An interval with float endpoints
can be thought of as the segment of the real line from the binary-represented
float a to the binary-represented float b, or as the set of points on that
line segment, or as a particular but unspecified element of that set.
Opinions differ on this, and they (eventually) matter to some degree.

Note that some numbers that you might type in like 0.1 are not exactly
representable in binary, and so if you type in 0.1, you are presenting
to the system some (other, nearby) number, not exactly equal to 1/10.

In Maxima you can also type in 1/10, which is exactly what it says.

If you want to enclose 1/10 by two nearby floats, you can create
it in various ways.  Here's one: ieval( 1.0d0*interval(1/10,1/10))
or  ieval(interval(1.0d0)/10);

We explain ieval in a moment.

Here's another.  widen(0.1d0,0.1d0) or just widen(0.1d0).

This also encloses 1/10, but it actually specifies enclosing some
other number. Just the enclosure ALSO does 1/10, since the usual
decimal-to-binary conversion is good to within 1/2 ULP (unit in the
last place), and the enclosure will go up and down 1 ULP.

The second important interface is ieval(expr)
where the given expression is evaluated using interval arithmetic.
If you ask for ieval(x+y*z) then x,y, and z must either evaluate
to intervals, or to scalar real numbers that can be interoperated with
intervals.  Ratios, integers, floats work.  Maybe later, bigfloats.
If there are any symbolic object in there, then ieval will give an
error message.

It is also possible to make intervals out of well-known constants, but
how much precision should be used?  We specify via the type and value
of intervalwidth

intervalwidth:2^(-53),  interval(%pi) ->[201/64,101/32]
intervalwidth:1.0e-8   interval(%pi)  ;;  27 bits = (ceiling(- (/ (log 1.0d-8) (log 2.0))))
intervalwidth: 1.0d15  interval(%pi)  ;;  50 bits

intervalwidth is NOT used in the case of interval() called on
a single or double float constant, or two of them.  In that case the
width is the tightest enclosure for which that floating format number
is definitely in the interior.
(For a non-zero double-float number this is produced by bumping up and down:
multiplying by one of (1+-double-float-epsilon). For zero,
the least positive normalized double float (or its negative) is used.)

We have implemented only %pi, so far. (And frankly, only up to 333 bits.)

What other kind of expressions are acceptable in the world of ieval?

x^n, sin(x), 1/x, and more.  There has to be some conduit from Maxima
to the interval package for each implemented mathematical function
extended to intervals. We have not implemented them all.

There are other kinds of expressions:  union, intersection, relations
such as possiblyGT, possiblyEQ, ...

There are selections, such as min(int) which is the lower bound, and
max(int) which is the upper.



Also of some note there are empty intervals, intervals which have
infinite endpoints, and "NotAnInterval".  Maxima is usually
able to accomodate unusual endpoints, although its treatment of
(for example) the floating-point "NaN" is not completely regularized
across different implementations of Lisp.




|#

#| Proposed rules for rounding up and rounding down, of a rational number.

1. If a number R can be exactly expressed as a double-float F, then rounding up or down
is an identity. E.g. 1/2 = 0.5d0 period.

2. If a number R cannot be expressed as a binary float exactly, then 2 other numbers
above and below R must be constructed.  Fdown and Fup.

There is a number double-float-epsilon
more easily grasped as   (2^52+1)/2^105  or in Lisp
(/(1+ (expt 2 52)) (expt 2 105)).

For pos rational number R, multiply exactly by (1+eps/2), then round to closet float. give upper bound.
Mmultiply it by (1-eps/2), rounding to closest float to give lower bound.
if R is negative, [l,u] -> [-u,-l]

Note that if R can be represented exactly as a float, there are 2 possible 1-ulp wide
intervals containing causing a problem with uniqueness. That is, 0.5 is in the interval
[0.4999..99, 0.5000...0]  but also in [0.5000...0, 0.5000...01]
|#


(defun downup(rin)
  (if (< rin 0)
      (reverse (mapcar #'(lambda(r)(- r))  (downup (- rin))))
  ;; really, should only be used for rational numbers.
    (let((r (reluctantrational rin))
       ;; these constants are computed at compile time.
       ;;let eps be the exact value for double-float-epsilon
       ;(hrateps #.(/(1+ (expt 2.0d0 52)) (expt 2 106))) ; this is half eps
       (halfepsup #.(+ 1 (/(1+ (expt 2 52)) (expt 2 106)))) ;; 1 + eps/2
       (halfepsdown #.(- 1 (/(1+ (expt 2 52)) (expt 2 106))));; 1- eps/2
       (fr 0.0d0) ;; float temp
       )
    (if (= (cl::rational (setf fr(* 1.0d0 r))) r) (list fr fr) ;; exact. otherwise
      (list (* 1.0d0 (* r halfepsdown))(* 1.0d0 (* r halfepsup)))))))


(defun testdu(r)  ;; test down up.  e.g. (testdu 1/2) (testdu 1/10) (testdu 1/3) (test 0.1d0)
  (let* ((h (downup r))
	 (low (car h))
	 (hi (cadr h)))
	
    (list :bounds (<= (setf low (cl::rational low)) r (setf hi (cl::rational hi)))
	  :tight (<= (/(- hi low) r) (* 2 double-float-epsilon) )
	  :verytight (<= (abs(/(- hi low) r))  double-float-epsilon) ; actually, must be equal
	  )))


(defun convwinf(g)  ;; convert the rational or integer number g to a double float, or inf.
  (handler-case (* 1.0d0 g)  ;; might overflow to +oo or -oo
    (simple-error (z) (if (> g 0) *d-inf* *dn-inf*))))

;;; we can't to convert inf, minf, NaN to rational.
;;; so we must multiply by them without the conversion to rational.
;;; or just do something like this:

(defun scalmultdown(a b)  ;; a and b are endpoints that are floats or oo or -oo or NaN.
  (cond ((nan-p a) a)
	((nan-p b) b)
	((inf-p a)(* a b))		; let the chips do the job , in case b is 0, give NaN)
	((inf-p b)(* a b))
	(t (down (* (cl::rational a)(cl::rational b))))))

(defun scalmultup(a b)  ;; a and b are endpoints that are floats or oo or -oo or NaN.
  (cond ((nan-p a) a)
	((nan-p b) b)
	((inf-p a)(* a b))		; let the chips do the job , in case b is 0, give NaN)
	((inf-p b)(* a b))
	(t (up (* (cl::rational a)(cl::rational b))))))

(defun scalmult(a b dir)  ;; a and b are endpoints that are floats or oo or -oo or NaN. dir =#'up or #'down
  (cond ((nan-p a) a)
	((nan-p b) b)
	((inf-p a)(* a b))		; let the chips do the job , in case b is 0, give NaN)
	((inf-p b)(* a b))
	((eq dir 'up)(up (* (cl::rational a)(cl::rational b))))
	((eq dir 'down)(down (* (cl::rational a)(cl::rational b))))
	((eq dir 'both) (list(down (setf a (* (cl::rational a)(cl::rational b))))
			     (up  a)))))


#+sbcl
(defun scalmult(a b dir) 
  (cond ((nan-p a) a)
	((nan-p b) b)
	((inf-p a)(* a b))		; let the chips do the job , in case b is 0, give NaN)
	((inf-p b)(* a b))
	((eq dir 'up)(with-rounding :positive-infinity (* a b)))
	((eq dir 'down)(with-rounding :negative-infinity (* a b)))
	((eq dir 'both) (with-rounding :positive-infinity (list (* a b) (- (* (- a) b)))))))
			

(defun reluctantrational(rin)
  (let ((r (cl::rational rin)))
    (if (not (rationalp rin))
	      (format t "~% coercing ~s to ~s"  rin r)) 
    r))

(defun down(rin) ;; round rational down to a double-float
  (if (< rin 0)
      (-(up (- rin)))
  ;; really, should only be used for rational numbers.
  (let((r (reluctantrational rin))
       ;; these constants are computed at compile time.
       ;;let eps be the exact value for double-float-epsilon
       (halfepsdown #.(- 1 (/(1+ (expt 2 52)) (expt 2 106))));; 1- eps/2
       (fr 0.0d0) ;; float temp
       )
    (if (= (cl::rational (setf fr(* 1.0d0 r))) r) fr ;; exact. otherwise
      (* 1.0d0 (* r halfepsdown))))))


(defun up(rin)
  (if (< rin 0)
      (- (down (- rin)))
  ;; really, should only be used for rational numbers.
  (let((r (reluctantrational rin))
       ;; these constants are computed at compile time.
       ;;let eps be the exact value for double-float-epsilon
       ;(hrateps #.(/(1+ (expt 2.0d0 52)) (expt 2 106))) ; this is half eps
       (halfepsup #.(+ 1 (/(1+ (expt 2 52)) (expt 2 106)))) ;; 1 + eps/2
       (fr 0.0d0) ;; float temp
       )
    (if (= (cl::rational (setf fr(* 1.0d0 r))) r)fr ;; exact. otherwise
      (* 1.0d0 (* r halfepsup))))))


(defun downup_s(rin) ;;; single float version
  (if (< rin 0)
      (reverse (mapcar #'(lambda(r)(- r))  (downup (- rin))))
  ;; really, should only be used for rational numbers.
    (let((r (reluctantrational rin))
       ;; these constants are computed at compile time.
       ;;let eps be the exact value for double-float-epsilon
       ;(hrateps #.(/(1+ (expt 2.0d0 52)) (expt 2 106))) ; this is half eps
       (halfepsup #.(+ 1 (/(1+ (expt 2 23)) (expt 2 48)))) ;; 1 + eps/2
       (halfepsdown #.(- 1 (/(1+ (expt 2 23)) (expt 2 48))));; 1- eps/2
       (fr 0.0e0) ;; float temp
       )
    (if (= (cl::rational (setf fr(* 1.0e0 r))) r) (list fr fr) ;; exact. otherwise
      (list (* 1.0e0 (* r halfepsdown))(* 1.0e0 (* r halfepsup)))))))

(defun downup_s(rin) ;;; single float version
  (if (< rin 0)
      (reverse (mapcar #'(lambda(r)(- r))  (downup (- rin))))
  ;; really, should only be used for rational numbers.
    (let((r (reluctantrational rin))
       ;; these constants are computed at compile time.
       ;;let eps be the exact value for double-float-epsilon
       ;(hrateps #.(/(1+ (expt 2.0d0 52)) (expt 2 106))) ; this is half eps
       (halfepsup #.(+ 1 (/(1+ (expt 2 23)) (expt 2 48)))) ;; 1 + eps/2
       (halfepsdown #.(- 1 (/(1+ (expt 2 23)) (expt 2 48))));; 1- eps/2
       (fr 0.0e0) ;; float temp
       )
    (if (= (cl::rational (setf fr(* 1.0e0 r))) r) (list fr fr) ;; exact. otherwise
      (list (* 1.0e0 (* r halfepsdown))(* 1.0e0 (* r halfepsup)))))))


(defun testdus(r)  ;; test down up.  e.g. (testdu 1/2) (testdu 1/10) (testdu 1/3) (test 0.1e0) ;;single
  (let* ((h (downup_s r))
	 (low (car h))
	 (hi (cadr h)))
	
    (list :bounds (<= (setf low (cl::rational low)) r (setf hi (cl::rational hi)))
	  :tight (<= (/(- hi low) r) (* 2 single-float-epsilon) )
	  :verytight (<= (abs(/(- hi low) r))  single-float-epsilon) ; actually, must be equal
	  )))




(defmacro gen-ieee-encoding (name type exponent-bits mantissa-bits)
  `(progn

    (defun ,(intern (format nil "~A-TO-IEEE-754"  name))  (float)
        (multiple-value-bind (significand expon sgn)
            (integer-decode-float float)
          (let* ((slen (integer-length significand))
                 (delta (- slen ,(1+ mantissa-bits)))
                 (sgn-norm (ash significand delta))
                 (ex (- (+ ,(+ mantissa-bits (1- (expt 2 (1- exponent-bits))) )
expon)
                        delta))
                 (output (if (minusp sgn) (dpb 1 (byte  1 ,(+ mantissa-bits
exponent-bits)) 0)
                       0))
           (final (if (not (plusp ex))
                      (dpb (ldb (byte ,mantissa-bits 0) (ash sgn-norm   (1- ex)))
                           (byte ,mantissa-bits 0)  output)
                      ;; or else .
                      (dpb (ldb (byte ,mantissa-bits 0) sgn-norm) (byte
,mantissa-bits 0)
                           (dpb ex (byte ,exponent-bits ,mantissa-bits) output)))))
            final)))


    (defun ,(intern (format nil "IEEE-754-TO-~A" name))  (ieee)
      (let* ((ex (ldb (byte ,exponent-bits ,mantissa-bits) ieee))
             (sig (ldb (byte ,mantissa-bits 0) ieee))
             (significand (if (zerop ex)
                              (ash sig 1)
                              (dpb 1 (byte 1 ,mantissa-bits) sig)))
             (ssigned (if (logbitp  ,(+ exponent-bits mantissa-bits) ieee)
                          (- significand)
                          significand))

             (aval
              (scale-float (coerce ssigned ,type)
                           (- ex
                              ,(+ (1- (expt 2 (1- exponent-bits)))
                                  (1- mantissa-bits)
                                  1
                                  )  ))))
        aval))
    ))
(gen-ieee-encoding float-32 'single-float  8 23)
(gen-ieee-encoding float-64 'double-float 11 52)

;;; now we have functions  (ieee-754-to-float-32 integer ) 
;;;  (ieee-754-to-float-64 integer)
;;; (float-32-to-ieee-754 single-float)
;;; (float-64-to-ieee-754 double-float)

;;;   to see a double-float number F in hex, do  
;; 
(defun showhex(f) (format nil "~x" (dtoint f)))
(defun dtoint(x) (float-64-to-ieee-754 x))
(defun inttod(x)(ieee-754-to-float-64 x))

;; (mapcar #'showhex (downup 1/10))
;; vs
;; (mapcar #'showhex (downup 0.1d0))

;; reading from a 3 string description of a float.  (fpscan "12" "34" -1) returns exactly 617/500, about 1.234
(defun fpscan(lft rt exp)
  (* (expt 10 (read-from-string exp))
     (+ (read-from-string lft) 
	(/ (read-from-string rt) (expt 10 (length rt))))))



;;; if we do all our arithmetic in double, but store only single,
;;; we can do things like this..

;;; this has width of 1 epsilon with naturally one endpoint
;;; being the single-float being enclosed.
;;;  start with rational input.

(defun downup_single(rin
		     &aux (up 0.0)(down 0.0)) ;;; single float version.  rin is single.
  (if (< rin 0)
      (reverse (mapcar #'(lambda(r)(- r))  (downup_single (- rin))))
    ;; really, should only be used for rational numbers.
    (let((r (coerce rin 'double-float))
       ;; these constants are computed at compile time.
       ;;let eps be the exact value for double-float-epsilon
       ;(hrateps #.(/(1+ (expt 2.0d0 52)) (expt 2 106))) ; this is half eps
       (halfepsup #.(+ 1 (/(1+ (expt 2 23)) (expt 2 47)))) ;; 1 + eps/2
       (halfepsdown #.(- 1 (/(1+ (expt 2 23)) (expt 2 47))));; 1- eps/2
	 )
      #+ignore
      (list (* 1.0e0 (rational r) halfepsdown)
	    (* 1.0e0 (rational r) halfepsup) )
      (list (setf down(* 1.0e0 (*(setf r (rational r))) halfepsdown))
	    (setf up (* 1.0e0 (* r halfepsup)))
	    ;; relative width
	    (abs (/ (- up down) (max up down)))
	    
	    ))))

(defun rnd(v)(* 1.0e0 (rational v))) ;; round to single

(defmethod dadd ((r real)(s real))	; produce a double float down-up enclosure from adding 2 reals
  (let* ((r (cl::rational r))
	 (s (cl::rational s))
	 (sum (+ r s))
	 (dsum (* 1.0d0 sum))
	 (resum (cl::rational dsum)))
  ;; sum is the true correct and complete rational sum of the two real numbers.
    ;; dsum is almost equal to sum
    
    (cond((= resum sum) ;; addition was exact, so dsum is the true sum also
	  (list dsum dsum))
	 ((> resum sum) ;; dsum is upper.
	  (list (bd dsum) dsum))
	 (t (list dsum (bu dsum))))))


(defmethod dmul ((r real)(s real))	; produce a double float down-up enclosure from multiplying 2 reals
  (let* ((r (cl::rational r))
	 (s (cl::rational s))
	 (prod (* r s))
	 (dprod (* 1.0d0 prod))
	 (reprod (cl::rational dprod)))
  ;; prod is the true correct and complete rational product of the two real numbers.
    ;; dprod is almost equal to prod
    
    (cond((= reprod prod) ;; mult was exact
	  (list dprod dprod))
	 ((> reprod prod) ;; dprod is upper.
	  (list (bd dprod) dprod))
	 (t (list dprod (bu dprod))))))
  

  
    

(defun intmul((r ri)(s ri))
	 (with-ri2		
	     r s (loA hiA decA)(loB hiB decB)

	     (let* ((lar (cl::rational loA))
		    (har (cl::rational hiA))
		    (lbr (cl::rational loB))
		    (lbr (cl::rational hiB))
		    (p1 (* lar lbr))
		    (p2 (* lar hbr))
		    (p3 (* har lbr))
		    (p4 (* har hbr))
		    (lowest (cl::min p1 p2 p3 p4))
		    (highest (cl:max p1 p2 p3 p4))
		    (dlo (* 1.0d0 lowest))
		    (dhi (* 1.0d0 highest))
		    (rdlo (cl::rational rdlo))
		    (rdhi (cl::rational rdhi)))
	       
	       
	       ;; if dlo is <= rdlo, we use dlo, else bump down.
	       
	       (ri (if (<= rdlo lowest) dlo  (bd dlo))
		   (if (>= rdhi highest) dhi (bu dhi))
		   (worst decA decB)))))
	       
	       
	       
		    
		    

