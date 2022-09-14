

;;; -*-  Mode: Lisp; Package: Maxima; Syntax: Common-Lisp; Base: 10 -*- ;;;;
;;; Richard Fateman 4/22/2016.  
;;; a better version, to use instead of makelist
;;; Adding "collect" as keyword in for i:1 thru 3 collect f(i)
;;; returns [ f(1), f(2), f(3) ].  All other keywords in for ... do
;;; work the same.
;;; 

;;; for i:1 next 2*i while i< 20 collect f(i)  is translated to
;;; block([g15:[]],
;;;      for i next 2*i unless i>=20 do  push(f(i),g15),
;;;      reverse(g15))

(in-package :maxima)
(load-macsyma-macros defcal mopers)

(def-lbp $collect	 25.)
(def-rbp $collect      25.)
(def-rpos $collect     $expr)

(def-collisions $do
    ($do	   . ())
  ($collect . ())
  ($for    . ($for))
  ($from   . ($in $from))
  ($in     . ($in $from $step $next))
  ($step   . ($in       $step $next))
  ($next   . ($in	$step $next))
  ($thru   . ($in $thru)) ;$IN didn't used to get checked for
  ($unless . ())
  ($while  . ()))

(def-nud-equiv $collect    parse-$do)

(defun parse-$do (lex &aux (left (make-mdo)))
  (setf (car left) (mheader 'mdo))
  (do ((op lex (pop-c))  (active-bitmask 0))
      (nil)
      (if (eq op '|$:|) (setq op '$from))
    (setq active-bitmask (collision-check '$do active-bitmask op))
    (let ((data (parse (rpos op) (rbp op))))
      (case op
	($do   	(setf (mdo-body left) data) (return (cons '$any left)))
	;; only change is the addition of the line below
	($collect   	(return (cons  '$expr (for-collect data left))))
	($for		(setf (mdo-for  left) data))
	($from		(setf (mdo-from left) data))
	($in		(setf (mdo-op   left) 'mdoin)
			(setf (mdo-from left) data))
	($step		(setf (mdo-step left) data))
	($next		(setf (mdo-next left) data))
	($thru		(setf (mdo-thru left) data))
	(($unless $while)
			(if (eq op '$while)
			    (setq data (list (mheader '$not) data)))
			(setf (mdo-unless left)
			   (if (null (mdo-unless left))
			       data
			       (list (mheader '$or) data (mdo-unless left)))))
	(t (parse-bug-err '$do))))))

(def-nud-equiv $for    parse-$do)	; reset parser to use the def above.

;; new function to handle the "collect" clause

(defun for-collect (data L)		;macro-expand the "for ..collect" into a do-loop
  (let ((newvar (gensym)))
    (setf (mdo-body L) `(($push)  ,data ,newvar))
    `((mprog)
      ((mlist)((msetq) ,newvar ((mlist)))) ; use local variable
      ,L
     (($reverse) ,newvar))))

      
       
	
