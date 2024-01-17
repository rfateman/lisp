(in-package :maxima)

(defun copy-if-list(x)
  (declare (optimize (speed 3)(safety 0)))
  (if(listp x)
     (copy-list x)
     x))


(defun simptimes (x w z)
					; W must be 1
  (declare (optimize (speed 3)(safety 0)))
  (prog (res check eqnflag matrixflag sumflag)
     (if (null (cdr x)) (return 1))
     (setq check x)
  start
     (setq x (cdr x))
     (cond ((zerop1 res)
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
	                    (not (member 'trunc (cdar w))))
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
	   ((member (caar w) '(mlist $matrix))
	    (setq matrixflag
		  (cond ((not matrixflag) w)
			((and (or $doallmxops $domxmxops $domxtimes)
			      (or (not (eq (caar w) 'mlist)) $listarith)
			      (not (eq *inv* '$detout)))
			 (stimex matrixflag w))
			(t
			 ;;(setq res (tms (copy-tree w) 1 (copy-tree res)))
			 (setq res (tms w 1 res)) ; no copy-tree at all

			 matrixflag)))
	    (go start))
	   ((and (eq (caar w) '%sum) $sumexpand)
	    (setq sumflag (sumtimes sumflag w))
	    (go start)))
     ;;(setq res (tms (copy-tree w) 1 (copy-tree res)))
    ;; (format t "~% w=~s" w)
     ;;(setq res (tms (copy-tree w) 1 res)) ;; only one copy-tree,copy-list no good ,, oscar says...
     (setq res (tms w 1 res))
     
     
     (go start)
  end
     (cond ((mtimesp res) (setq res (testt res))))
     (cond (sumflag (setq res (cond ((or (null res) (equal res 1)) sumflag)
				    ((not (mtimesp res))
				     (list '(mtimes) res sumflag))
				    (t (nconc res (list sumflag)))))))
     (cond ((or (atom res)
		(not (member (caar res) '(mexpt mtimes)))
		(and (zerop $expop) (zerop $expon))
		*expandflag*))
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
			               (not (member res '(-1 -1.0))))
			          ;; RES should only be -1 here (not = 1)
                                  (and $domxmxops
                                       (member res '(-1 -1.0))))
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
;;;;;;;;;
;; maybe look at this.......


;;; also needed for oscar patch...
(defun tms (factor power product &aux tem)
    (declare (optimize (speed 3)(safety 0)))
  (let ((*rulesw* nil)
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
	       (setq tem (copy-if-list tem))
	       tem))
	  ((mtimesp factor)
	   (do ((factor-list (cdr factor) (cdr factor-list)))
	       ((or (null factor-list) (zerop1 product))  product)
	     (setq z (timesin (car factor-list) (cdr product) power))
	     (when *rulesw*
	       (setq *rulesw* nil)
	       ;;(setq product (tms-format-product z))
	       (setq product (tms-format-product (copy-if-list z)))
	       )))
	  (t
	   (setq z (timesin factor (cdr product) power))
	   (if *rulesw*
	       (tms-format-product z)
	       product)))))

