;; Making simplus faster by modest changes.
;;; joint work by Barton Willis and Richard Fateman
;;;  7/23/06 4:44PM PST RJF

;;; fiddled with on 1/12/2013 with new ACL and Maxima 5.29.1  RJF
;;; was mzsimpfast.lisp on c:/lisp
;;; fixed up to work on 01/21/2013 RJF


;;; ADDING IN HASH TABLE, 
;;; PUTTING in UNIQUE stuff, changes marked by  **  7/23/07 RJF

;;; REDOING HASH TABLE according to Duane Rettig's suggestions for shared-cons
;;; in Allegro CL 8.0, patched to 8/1/2006 for faster hashing.

;;; ALSO uses to use fastgreat/ ordering by tree insertion etc.
;;; rewrote etree-si, changed dosum to use hash table.  (need to repair dosum-prod)
;;; seems to be rather fast now.

(in-package :maxima)
(eval-when (compile)(declaim (optimize (speed 3)(safety 1)(space 0)#+allegro(debug 0))
			     (special *uniq-table*)))

(define-modify-macro mincf (&optional (i 1)) addk)
;;(eval-when (compile)
;;  (defmacro memq(x list)  `(member ,x ,list :test #'eq)))

(defmfun eqtest (x check)
  (let ((y nil))
    (uniq ;; change from simp.lisp
     (cond ((or (atom x)
	       (eq (caar x) 'rat)
	       (eq (caar x) 'mrat)
	       (member 'simp (cdar x) :test #'eq))
	   x)
	  ((and (eq (caar x) (caar check))
		(equal (cdr x) (cdr check)))
	   (cond ((and (null (cdar check))
		       (setq y (get (caar check) 'msimpind)))
		  (cons y (cdr check)))
		 ((member 'simp (cdar check) :test #'eq)
		  check)
		 (t
		  (cons (cons (caar check)
			      (if (cdar check)
				  (cons 'simp (cdar check))
				  '(simp)))
			(cdr check)))))
	  ((setq y (get (caar x) 'msimpind))
	   (rplaca x y))
	  ((or (member 'array (cdar x) :test #'eq)
	       (and (eq (caar x) (caar check))
		    (member 'array (cdar check) :test #'eq)))
	   (rplaca x (cons (caar x) '(simp array))))
	  (t
	   (rplaca x (cons (caar x) '(simp)))))
       *uniq-table*)))


(defun zerop1(x)
 (cond ((numberp x)(= 0 x))
       (($bfloatp x)(= 0 (second x)))))

;; redefined as macro, maybe slightly faster?? breaks other stuff tho.
;; this does not work for CRE zero e.g.  rat(x-x).
#+ignore
(defmacro zerop1(x)
   `(let ((g% ,x))
     (cond ((numberp g%)(= 0 g%))  ;; note, if maxima has rationals like ((rat) 1 2) those are not zero
       (($bfloatp g%) (= 0 (second g%))))))

(defun onep1(x)(or (and (numberp x)(= x 1)) (and ($bfloatp x) (onep1bf x))))
(defun minusp1(x)(or (and (numberp x)(= x -1)) (and ($bfloatp x) (minusonep1bf x))))

(defun onep1bf(b)			;b is a bigfloat. return t iff b is 1.0b0
  (= (cadr b) (ash 1 (1-(caddar b) ))) )
(defun minusonep1bf(b)			;b is a bigfloat. return t iff b is -1.0b0
  (= (cadr b) (ash -1 (1-(caddar b) ))) )

(defun convert-to-coeff-form (x table) ;;add x into table: derive from x
  ;; a key and value (key= kernel value= {number +previous value}).
  ;; each item x is either a number, a symbol, say w, or ((mtimes) 3
  ;; w) or ((mtimes) 3 w z..) or ((mtimes) w z..)  or ((--not mtimes)
  ;; ...)  treated like ((mtimes) 1 ((--not mtimes ) ...)
  (let ((c))
    (cond ((mnump x) (minsert 1 x table)) ;; If x is just a number the KEY is 1
	  ((mtimesp x)
	   (pop x)  ;remove (car x) which is (mtimes ..)
	   (cond ((mnump (setf c(car x))) ;set c to numeric coeff. Could be integer, rat, float
		  (pop x) ; remove numeric coeff.
		  (if (null (cdr x));; if only one more item, that's it.
		       ;; if 3*z, the key is z, the coef is 3
		      (minsert (car x) c table)
		    ;; more than one more item. multiply them 
		    (let ((v  `((mtimes simp) ,@x)))
		      (minsert v c table)))) ;; if 3*w*z, the key is w*z, the coef is 3
		 ;; no explicit numeric coefficient , so it is 1
		 (t (let ((v   `((mtimes simp) ,@x))) ;;**  if w*z, the key is w*z, the coef is 1
		      (minsert v 1 table)))))
	  ;; not an mtimes at all.
	  (t  (minsert x 1 table))))) ;; the key is, say sin(z), the coef is 1.

;;; we needed to fix a bug here in that  3*(a+b)+ (-2)*(a+b)  will leave in ht, key=(a+b), val=1,
;;; whereas it should leave  key=a val=1, key=b val=1.
;;; minsert should do it.

(defun minsert(key val ht)
  (setf key (uniq key *uniq-table*)) ;; ** often no-op?? The key must be unique to use hashing effectively
  (let ((theval(mincf (gethash key ht 0) val))) ; increment oldval [or 0] by val
    (cond ((zerop1 theval)(remhash key ht)) ;if new val after increment is zero, remove entry
	  ;; now check the key
	  ((mplusp key);; if the key is itself a sum, we must expand it into the table.
	   ;;here's the situation.  Previously we had something like 3*(a+b+...), which is
	   ;; OK, key = a+b+..., value = 3.  But we just added in -2*(a+b+...) and so
	   ;; We (now) have 1*(a+b+...).  We must remove this entry and insert 1*a and 1*b etc.
	   ;if new value is 1, and key = a+b+...
	   (cond ((onep1 theval) 
		  (remhash key ht)
		  (dolist (k (cdr key))
		    (convert-to-coeff-form k ht)))
		 ((minusp1 theval) ;if new value is -1,  ;; any version of -1, similarly.
		  (remhash key ht)
		  (dolist (k (cdr key))
		    (minsert k -1 ht))))))))

  
(defun newsimplus (l)
  (let ((h (make-hash-table :test #'eq)) ;; **
	)
    ;; convert each entry in h to coeff form and insert in table
    (dolist (j (cdr l))(convert-to-coeff-form j h))
    ;; take the terms out and sort them
    (hash-to-sorted-list h '(mplus simp))))

(defun hash-to-sorted-list(h thecar)
  (let ((terms nil))
    (maphash #'(lambda(key val)
		 (cond((equalp val 1)(push  key terms))
		      (t (push (uniq (mul val key) *uniq-table*) terms))))
	     h)
    
  ;;  (setf globterms (copy-list terms))
    ;; this next line is necessary if you want to really
    ;; simplify the result, not just what Maple does.
    ;; Unfortunately it takes about half the total time.
    ;;   (setf terms (sort terms #'$orderlessp))
    (setf terms (nreverse (sort terms #'newgreat)))
    (cond ((null terms) 0)
	  ((null (cdr terms)) (car terms))
	  (t (cons thecar terms)))))


(defun lengthless(x len) 
  ;; returns t if length of x is less than len
  ;; otherwise returns nil
  ;; like  (< (length x) len)
  ;; but maybe faster??
  (declare (fixnum len)(optimize (speed 3)(safety 0)))
  (cond ((null x) t)
	((= len 0) nil)
        (t(lengthless (cdr x) (1- len)))))

(defun complicated-plus (x)
  ;; test to see if there is some complicated component
  ;; that requires the original simplus to be used.
  (let ()
    (dolist (j (cdr x) nil) ;return nil if everything was found uncomplicated!
      (and (consp j)
	   (case (caar j)
	     ((mrat mequal mlist $matrix %sum)
	      (return t)))))))

;;;; this next definition is copied from the file simp.lisp
;;;; and then altered just a little.

;; there are several special cases handled by simplus. (comments by rjf)

;; equations + scalars
;;  v +(a=b)  -> v+a = v+b
;; (a=b) + (c=d) =  a+c = d+b

;; matrices (or lists)  + scalars or matrices
;; v+matrix([a,b],[c,d]) -> matrix([a+v,b+v],[c+v,d+v])
;; matrix(..)+matrix(...)-> sum of matrices if sizes are the same.
;; v+ [a,b,c] -> [v+a,v+b,v+c]
;; if list or matrix size incompatibilities occur, error from "fullmap"

;; matrix (or lists)  + equation
;; (a=b)+matrix produces  (matrix+a)=(matrix+b)

;; mrat form (canonical rational form)
;; mrat(e) + anything -> rat (e+anything)

;;%sum form
;; sum(a[i],i,1,n)+sum(a[i],i,n+1,m) -> sum(a[i],i,1,m)
;; (this is done by sumpls, and the circumstances have to be just right
;; to make it happen)

;; various other combinations are also handled.

;; sum+(a=b) -> sum+a = sum+b
;; sum+matrix -> matrix of (entry[i,j]+sum).
;; mrat+sum -> mrat, with one "rational variable" being a sum.
;; mrat+matrix -> matrix of (entry[i,j]+ "disrep'd" mrat).

;;  this kind of treatment is really uncomfortable.  add a new
;; data type and you have to make n coercion decisions and/or
;;  break the program. 

;; examples of broken-ness: 
;; a+b*%i+c+d*%i -> %i*d+c+%i*b +a.
;; interval(a,b)+interval(a,b) -> 2*interval(a,b)
;; infinity+infinity-> 2*infinity;  (limit(2*infinity) -> infinity, though)

;; an apology for the structure of the program -- it even has goto and
;; labels!  it was originally written by knut korsvold, circa 1963
;; when Lisp was 3 years old and people didn't know better. -- rjf

(defmfun simplus (x w z)		; W must be 1
  (prog (res check eqnflag matrixflag sumflag ;(len 0) 	 
	     (terms nil) (h nil))
    (declare  (optimize(speed 3)))
    (if (endp (cdr x)) (return 0))
    (if (endp (cddr x))(return (simplifya (cadr x) nil)))
    (setq check x)
    ;; simplify subexpressions unless z=t
    ;; also don't count length of x in len
    (if z nil (setf x (dolist (i (cdr x) (cons (car x) terms))
			;;(incf len)
			(setf h (uniq (simplifya i nil) *uniq-table*)) ;**
			(cond ((mplusp h) (dolist (k (cdr h))(push k terms)))
			      (t (push h terms)))
		;;	(format t "~% terms=~s"  terms)
			)))
    ;; this diversion to newsimplus was added for making plus faster for long expressions
    ;; maybe we should also avoid newsimplus for shortish expressions?
    (if (or (lengthless x 8)(complicated-plus x)) nil ;; if too complicated for hack or too short, Fall through.
      (return (newsimplus x)))	;try new hack for simplus
    ;; this is the same as the old simplus except for line **
    ;;
   start(setq x (cdr x))
    (if (null x) (go end)) 
    (setq w (car x)) ;** w already simplified
   st1  (cond
	 ((atom w) nil)
	 ((eq (caar w) 'mrat)
	  (cond ((or eqnflag matrixflag
		     (and sumflag (not (memq 'trunc (cdar w))))
		     (spsimpcases (cdr x) w))
		 (setq w (ratdisrep w)) (go st1))
		(t (return (ratf (cons '(mplus)
				       (nconc (mapcar #'simplify (cons w (cdr x)))
					      (cdr res))))))))
	 ((eq (caar w) 'mequal)
	  (setq eqnflag
	    (if (not eqnflag)
		w
	      (list (car eqnflag)
		    (add2 (cadr eqnflag) (cadr w))
		    (add2 (caddr eqnflag) (caddr w)))))
	  (go start))
	 ((memq (caar w) '(mlist $matrix)) 
	  (setq matrixflag
	    (cond ((not matrixflag) w)
		  ((and (or $doallmxops $domxmxops $domxplus
			    (and (eq (caar w) 'mlist) ($listp matrixflag)))
			(or (not (eq (caar w) 'mlist)) $listarith))
		   (addmx matrixflag w))
		  (t (setq res (pls w res)) matrixflag)))
	  (go start))
	 ((eq (caar w) '%sum)
	  (setq sumflag t res (sumpls w res))
	  (setq w (car res) res (cdr res))))
    (setq res (pls w res))
    (go start)
   end  
    (setq res (testp res))
    (if matrixflag
	(setq res (cond ((zerop1 res) matrixflag)
			((and (or ($listp matrixflag)
				  $doallmxops $doscmxplus $doscmxops)
			      (or (not ($listp matrixflag)) $listarith))
			 (mxplusc res matrixflag))
			(t (testp (pls matrixflag (pls res nil)))))))
	(setq res (eqtest res check))
	(return (if eqnflag
		    (list (car eqnflag)
			  (add2 (cadr eqnflag) res)
			  (add2 (caddr eqnflag) res))
		  res))))

;; very minor change
(defmacro memqarr (l) `(if (memq 'array ,l) t))

#+ignore
(defun alike1 (x y)
  (declare (optimize (speed 3)(safety 0)#+allegro (debug 0)))
  (cond ((eq x y))
	((atom x) (equal x y))
	((atom y) nil)
	(t (and (consp(car x))
		(consp(car y))
		(eq (caar x) (caar y))
		(eq (memqarr (cdar x)) (memqarr (cdar y)))
		(alike (cdr x) (cdr y))))))

;;;*** changed !!!
(defun alike1 (x y)
  (declare (optimize (speed 3)(safety 0)#+allegro (debug 0)))
  (cond ((consp x)(eq x y)) ;; the only way it could be equal, if hcons used
	((consp y) nil)
	(t (equal x y)))) ; symbols, numbers, strings?

;;;;;;;;;;; uniquification... (sp?)

;; (c) 1990, 1991, Richard J. Fateman
;; (c) 1994 Richard J. Fateman
;; re-edited  10/2003 RJF
;; again, 7/23/2006 RJF
;; again, 8/1/2006 RJF  from Duane Rettig suggestions.

#+allegro
(setq *uniq-table*
  (make-hash-table :size 10000 :test #'equal :weak-keys :tenurable :values nil))
#-allegro (setq *uniq-table*
  (make-hash-table :size 10000 :test #'equal))

;; maybe not use this...
#+ignore
(let (cell);; reusable local cons or nil
  (defun ucons (one two &aux tcell)
    (cond (cell
	    (setf (car cell) one (cdr cell) two)
	    (setq tcell cell cell nil));; make reentrant
	  (t (setq tcell (cons one two))
	     ;; At this point cell is nil (for mp) and tcell holds a cons to share
	     ;; If another process puts another cons at cell, we don't care.
	     (let ((scell (uniq tcell *uniq-table*)));; [could cause consing]
	       (when (and (not (eq scell tcell)) (null cell))
		 ;; The cons had been stored, and no other process has stored a
		 ;; new scratch cell; nil-out and reuse this cons
		 (setf (car tcell) nil (cdr tcell) nil)
		 (setq cell tcell))
	       scell)))))


;;but the above definition turns out to be thread-unsafe, so we just define it thus:
;; sometimes wasting a cons which will get collected really soon anyway.

(defun ucons (one two)
  (uniq (cons one two) *uniq-table*))

#+allegro  ;; GCL has no weak keys. SBCL  and CLISP do.  
(setq *uniq-table*
  (make-hash-table :size 200 :test #'equal :weak-keys :tenurable :values nil))

#+SBCL(setq *uniq-table*
  (make-hash-table :size 200 :test #'equal :weak-keys ))

#+GCL
(setq *uniq-table*
  (make-hash-table :size 200 :test #'equal))


#+allegro
(defvar *uniq-atom-table* (make-hash-table :test #'eql :values nil))
#-allegro
(defvar *uniq-atom-table* (make-hash-table :test #'eql ))

(defun uniq (obj table)
  "Return a canonical representation that is EQUAL to x,
  such that (equal x y) => (eq (uniq x *uniq-table* (uniq y *uniq-table*))"
    (declare (optimize (speed 3)(safety 0)(debug 0)))
  (typecase obj
    ((or fixnum symbol) obj)
    (atom (or (gethash obj *uniq-atom-table*)
              (setf (gethash obj *uniq-atom-table*) obj)))
    (cons
     (let ((hobj (gethash obj table)))
       (when hobj
	 (return-from uniq hobj)))
     (let ((newcar (uniq (car obj) table))
	   (newcdr (uniq (cdr obj) table)))
       (unless (and (eq newcar (car obj)) (eq newcdr (cdr obj)))
	 (setq obj (cons newcar newcdr)))
       #+allegro
       (excl:puthash-key obj table)
       #-allegro
       (setf (gethash obj table) obj)
       )))
					;obj
  )


(defun umapcar(f x)(cond((null x)nil)
			(t (ucons (funcall f (car x))(umapcar f (cdr x))))))
(defun uappend(r s)(cond ((null r)s)
			 (t (ucons (car r)(uappend (cdr r) s)))))

;; debugging
(defun dispuniq()(maphash #'(lambda(key val)(displa (cons key val))) *uniq-table*))
(defun listuniq()(maphash #'(lambda(key val)(format t "~s~%"
						    (cons key val))) *uniq-table*))

(defun $uniq(x)(uniq x *uniq-table*))

#| Duane says..


(defvar *shared-cons-table*
  (make-hash-table :size 200 :test #'equal :weak-keys t :values nil))
    
and the function to ensure that the conses are all in the table would
be: 

(defun share-conses (obj &optional (table *shared-cons-table*))
  (cond ((consp obj)
	 (let ((hobj (gethash obj table)))
	   (when hobj
	     (return-from share-conses hobj)))
	 (let ((newcar (share-conses (car obj) table))
	       (newcdr (share-conses (cdr obj) table)))
	   (unless (and (eq newcar (car obj)) (eq newcdr (cdr obj)))
	     (setq obj (cons newcar newcdr)))
	   (puthash-key obj table)))
	(t obj)))

Finally, you would use a function called shared-cons to cons up a cons cell that is guaranteed to be both in the hash table and having uniqure contents wrt other conses.  We started out with this definition, to avoid any ephemeral consing:

(let (cell) ;; reusable local cons or nil
  (defun shared-cons (one two &aux tcell)
    (if* cell
       then (setf (car cell) one (cdr cell) two)
	    (setq tcell cell cell nil) ;; make reentrant
       else (setq tcell (cons one two)))
    ;; At this point cell is nil (for mp) and tcell holds a cons to share
    ;; If another process puts another cons at cell, we don't care.
    (let ((scell (share-conses tcell))) ;; [could cause consing]
      (when (and (not (eq scell tcell)) (null cell))
	;; The cons had been stored, and no other process has stored a
	;; new scratch cell; nil-out and reuse this cons
	(setf (car tcell) nil (cdr tcell) nil)
	(setq cell tcell))
      scell)))

but the above definition turns out to be thread-unsafe, so we just define it thus:

(defun shared-cons (one two)
  (share-conses (cons one two)))

and let it cons an ephemeral cell.  You might be able to use the non-consing version anyway.

The above functions and tables are real in Allegro CL and are in the excl package, but I recommend that you do not use them because the shared-cons hash-table is rather large and might slow down your operation.

I'd like for you to try this one out, before I send you the hashstats function - perhaps this one is faster itself.  puthash-key only generates the index once, so in a sense it isdoing precisely what you want it to do.  But I had never thought of it that way, since I had never looked at it as a way to speed things up; only to make things more space efficient.  But sometimes you get both ...

Two more issues:

 1. Be sure you're up-to-date with patches; there is a hash.xxx patch that speeds up sxhash for conses.

 2. The real definition of excl::*shared-cons-table* is

(setq *shared-cons-table*
  (make-hash-table :size 200 :test #'equal :weak-keys :tenurable :values nil))
|#

;;; more changes to simp.lisp 
;;; hacking great
(eval-when (compile)
   (declaim (optimize (speed 3) (safety 1) (space 0) (compilation-speed 0))))
  ;;(use-package climax)
;; lots of stuff in nnewsimp.cl were taken out (instead of debugged)
;;**********************************************************************;;
;; shortcut to greatness
(defvar *great-tree* nil)
(defvar *great-etree* nil)

#+allegro
(defvar *great-hash*   (make-hash-table :size 2000 :test #'equal :weak-keys :tenurable))
#-allegro
(defvar *great-hash*   (make-hash-table :size 2000 :test #'equal))

(defun newgreat (x y)
  (declare (optimize (speed 3)(safety 0)))
 (cond ((atom x)
	(cond ((atom y)
	       ;; both x and y are atoms.
	       (if (numberp x)
		   ;; x is a number
		   (if (numberp y) 
		       ;; x and y are numbers
		       (if (or(complexp x)(complex y))
			   ;; atleast one of x and y is a complex number. 
			   ;; unlikely since maxima does not use CL complexes
			   (complex-great x y)
			 ;; compare x and y numerically. presumably 
			 ;; x=y excluded by previous tests, if that mattered
			 (> x y))
		     ;; x is a number but y is not a number.
		     nil)
		 ;; order numbers by value; complexes by real then im.

		 (fastgreat x y) ) ;; x and y are atoms but not numbers
	       )
	      ;; x is an atom but y is not an atom.
	      (t (fastgreat x y))
	      ))
       ;; x is not atom 
       ((numberp y) t) ;; but y is a number
       ;; neither x nor y is a number (or atom).
       (t  (fastgreat x y))))

(defun complex-great (x y)(cond
			   ((> (realpart x)(realpart y)) t)
			   ((eql (realpart x)(realpart y))
			    (> (imagpart x)(imagpart y)))
			   ;; either equal or <. 
			   (t nil)))

(defun fastgreat (a b)
  (> (the fixnum (etree-si a #'great-comp))
     (the fixnum (etree-si b #'great-comp))))
    

;; new tree routine wants cmp similiar to 'strcmp'

(defun great-comp (a b)
 (let ((res
	(cond ((eq a b) 0)
	      ((great a b) 1)
	      (t -1))))
   ;set temporary position for "a" in hashtable
  ;; (setf (gethash a *great-hash*)(+ res (gethash b *great-hash*)))
   res))


;;;;;;;;;;;;;;;;;;;;
;;(in-package "maxima")
;;;...... tree stuff from nt.lisp
;; maintain in synchrony a tree tr = *great-tree*
;;  and a  hash table ht = *great-hash*.
;; we have a comparison function that we use for insertion into the
;; tree, but to find out the ordering of two entries a b, we use.

;; (> (gethash a ht) (gethash b ht))

;; if we don't know if the items are in the hashtable, we do
;; (> (etree-si a #'comp) (etree-si b #'comp))
;;
;; note: this uses just binary search tree.

;; search: o(1) if already there.
;; insert: usual o(log n) time, worst-case o(n) time


;;**********************************************************************;;


(defstruct (etree (:print-function etree-print))
  (left  nil) (right nil)  number data)

(defun etree-print (etree str ind)
  (unless (null etree)
	  (etree-print (etree-left etree) str (1+ ind))
	   ;; tab to ind column, then print this datum
	  (format str "~vt~s~%" ind (etree-data etree))
	  (etree-print (etree-right etree) str (1+ ind))))

(defun etree-si (data comp)
  (if (and (consp data)(not (gethash data *uniq-table*))) (format t "~% not unique ~s" data))
  ;search or insert
  (or (gethash data *great-hash*)
      ;; insert using largest span. 
      (etree-i data comp *great-etree* 
	       #.most-negative-fixnum
	       #.(1- most-positive-fixnum) ))) ;; make it even, to start.

#+ignore
;;; the respace algorithm had bugs. dont' use it.
(defun etree-i (data comp tree lo hi)
  (case (funcall comp data (etree-data tree))
    (0 (format t "~%warning ~s found in tree but not hashtable" data)
					; maybe an error, should have found it in the hash table!
       (etree-number tree))		; use this number tho
    (-1
     (cond ((etree-left tree)		; is there a left tree?
	    (etree-i data comp (etree-left tree) lo (etree-number tree)))
	   ;; there is no left tree so we must make one
	   (t(let ((av (+ (ash lo -1)(ash (setf hi (etree-number tree)) -1))));average
	       ;;    (format t "~%av =~s" av)
	       (cond ((< lo av hi)	; ok to insert here
		      (setf (etree-left tree)
			    (make-etree :data data
					:left nil
					:right nil
					:number av))
		      (setf (gethash data *great-hash*) av)
		      )
		     (t			; failed to interpolate
		      (respace)
		      (etree-si data comp)))))))
    (1
     (cond ((etree-right tree)		; is there a right tree?
	    (etree-i data comp (etree-right tree) (etree-number tree) hi))
	   ;; there is no left tree so we must make one
	   (t(let ((av (+ (ash (setf lo(etree-number tree)) -1)(ash hi -1))));average
	       (cond ((< lo av hi)	; ok to insert here
		      (setf (etree-right tree)
			    (make-etree :data data
					:left nil
					:right nil
					:number av))
		      (setf (gethash data *great-hash*) av))
		     (t			; failed to interpolate
		      (respace)
		      (etree-si data comp)))))))))

 ;; rational interpolation never fails
(defun etree-i (data comp tree lo hi)
  (case (funcall comp data (etree-data tree))
    (0 (format t "~%warning ~s found in tree but not hashtable" data)
					; maybe an error, should have found it in the hash table!
       (etree-number tree))		; use this number tho
    (-1
     (cond ((etree-left tree)		; is there a left tree?
	    (etree-i data comp (etree-left tree) lo (etree-number tree)))
	   ;; there is no left tree so we must make one
	   (t(let ((av (* 1/2 (+ lo (etree-number tree)))))
	       ;;    (format t "~%av =~s" av)
	        (setf (etree-left tree)
			    (make-etree :data data
				;;	:left nil :right nil
					:number av))
		 (setf (gethash data *great-hash*) av)))))
    (1
     (cond ((etree-right tree)		; is there a right tree?
	    (etree-i data comp (etree-right tree) (etree-number tree) hi))
	   ;; there is no left tree so we must make one
	   (t(let ((av (* 1/2 (+ (etree-number tree) hi))))
	        (setf (etree-right tree)
			    (make-etree :data data
					;;:left nil :right nil
					:number av))
		 (setf (gethash data *great-hash*) av)))))))

;; try this
(defun comp(a b)(cond((eq a b) 0) ((maxima::alphalessp a b) -1)(t 1)))

(defun respace ( &aux (etree *great-etree*) (table *great-hash*) )
 (let*
    ((size (hash-table-count table))
     (arr (etree2arr etree size))	;temp array
     ;allocate new table, to hold the contents formerly in *great-hash* table
     (ht  (make-hash-table :size (* 2 size) :test #'eq)) 
     (increment (truncate  (- most-positive-fixnum most-negative-fixnum) 
			   (+ size 1))); space everything evenly apart
     (d nil))
   
  ;; (break t  "respace")

   ;; set up the new values in the hash table
   (do ((j 0 (1+ j))
	(newval (+ increment most-negative-fixnum)
		(+ newval increment)))
       ((= size j) nil)
     (declare (fixnum j increment newval))
					;(format t "hash[~s] set to ~s~%" j newval)
    
     (cond ((etree-p  (setf d (svref arr j))) ;; the node
	    (setf (gethash (etree-data d) ht) newval) ;replace old data in *great-hash*
	    (setf (etree-number d) newval)))) ; put number into etree node, too.
	   ;; set up the new etree
	   (setf *great-etree* (arr2etree arr))
   ;; point to the new hash-table
   (setf *great-hash* ht)
   'alldone
   ))

 ;; make an array of nodes.
 
 ;;etree2arr converts a (presumably sorted) etree of h entries
;; to an array a[0..(h-1)].

(defun etree2arr (tr size);; size = number of entries in the etree
  (let ((res (make-array size)) (count 0))
    (labels ((t2a(node)
		 (unless (null node)
		   (t2a (etree-left node))
		   (setf (etree-left node) nil)
		   (setf (svref res count) node)
		   (incf count)
		   ;; (if (= count size) "etree was bigger than u thought")
		   (t2a (etree-right node))
		   (setf (etree-right node) nil))))
      (t2a tr))
    res))


(progn (setq *great-etree* (make-etree :data 'origin :number 0))
       (setq *great-hash* (make-hash-table :test #'eq))
       (setf (gethash 0 *great-hash*)0))

#|
;; some tests for respace
(defun regreat()
  (progn (setq *great-etree* (make-etree :data 'origin :number 0))
       (setq *great-hash* (make-hash-table :test #'eq))
       (setf (gethash 0 *great-hash*)0)))

(defun test2 (L) (mapc #'(lambda(x)(etree-si x #'gcomp)) L))
(test2 '(a b z v b))

(defun gcomp(a b)
  (cond ((eq a b) 0)((great a b) 1)(t -1)))
|#

(defun l (a) ;return the order number of a
  (etree-si a #'comp))

(defun ci() ;check it out
  (format t "~% hash=~%")
  (listhash *great-hash*)
  )

;;;; this is just the old program, still in use.. ug
(defun great (x y)
 ;;(declare (object y))
 (cond ((atom x)
	(cond ((atom y)
	       (cond 
		     ((numberp x)
		      (cond ((numberp y)
			     (setq y (- x y))
			     (cond ((zerop y) (floatp x)) (t (plusp y))))))
		     ((constant x)
		      (cond ((constant y) (alphalessp y x)) (t (numberp y))))
		     ((mget x '$scalar)
		      (cond ((mget y '$scalar) (alphalessp y x)) (t 
								  (maxima-constantp y)
	 							  )))
		     ((mget x '$mainvar)
		      (cond ((mget y '$mainvar) (alphalessp y x)) (t t)))
		     (t (or (maxima-constantp y) (mget y '$scalar) 
			    (and (not (mget y '$mainvar)) (alphalessp y x))))))
	      (t (not (ordfna y x)))))
       ;; x is NOT an atom, but y is an atom
       ((atom y) (ordfna x y))
       ((eq (caar x) 'rat)

	(cond ((eq (caar y) 'rat)
	       ;; both x and y are rational numbers
	       (> (* (caddr y) (cadr x)) (* (caddr x) (cadr y))))))
       ((eq (caar y) 'rat))
       ((memq (caar x) '(mbox mlabox)) (great (cadr x) y))
       ((memq (caar y) '(mbox mlabox)) (great x (cadr y)))
       ((or (memq (caar x) '(mtimes mplus mexpt %del))
	    (memq (caar y) '(mtimes mplus mexpt %del)))
	(ordfn x y))
       ((and (eq (caar x) 'bigfloat) (eq (caar y) 'bigfloat)) (mgrp x y))
       (t (do ((x1 (margs x) (cdr x1)) (y1 (margs y) (cdr y1))) (())
	      (cond ((null x1)
		     (return (cond (y1 nil)
				   ((not (alike1 (mop x) (mop y)))
				    (great (mop x) (mop y)))
				   ((memq 'array (cdar x)) t))))
		    ((null y1) (return t))
		    ((not (alike1 (car x1) (car y1)))
		     (return (great (car x1) (car y1)))))))))

;; look at hash table

(defun listhash(h)(maphash #'(lambda(key val)(format t "~s -> ~s~%"
						    key val)) h))



;;arr2etree convert a (presumably sorted) array of nodes into a etree.

(defun arr2etree(a)
  (labels ((a2t (lo hi)
		(cond ((> lo hi) nil)
		      ((and (= lo hi) (etree-p (svref a lo)))
		       (make-etree :data  (etree-data (svref a lo))
					     :number lo))
		      (t (let((m (ash (+ lo hi)-1))); (lo+hi)/2 truncated
			   (if (etree-p (svref a m))
			   (make-etree :data (etree-data (svref a m))
				       :left (a2t lo (1- m))
				       :right (a2t (1+ m) hi)
				       :number m )))))))
    (a2t 0 (1- (length a)))))


(eval-when (compile load)(declaim (special *uniq-table*)))
(loop for k in '(mplus mtimes mexpt) do  
      (setf (get k 'msimpind)(uniq (get k 'msimpind) *uniq-table*)))

(defun maxima-constantp(x)(constantp x))  ;;; what should this really be??


(defun dosum (exp ind low hi sump &key (evaluate-summand t))
  (if (eq sump t) (dosum-sum exp ind low hi) (dosum-prod exp ind low hi)))
(defun dosum-prod (exp ind low hi) 
  (declare (ignore exp ind low hi))
  (error "We have to rewrite dosum for dosum-prod"))

  ;; separate sums and products for now.
(defun dosum-sum (exp ind low hi)  
  (declare (special $sumhack))
  (if (not (symbolp ind))
      (merror "improper index to sum~m"  ind))
  (unwind-protect 
      (prog (*i u lind l*i *hl)

	;; leave out sumhack check

	    (assume (list '(mgeqp) ind low))
     
	    (if (not (eq hi '$inf))
		(assume (list '(mgeqp) hi ind)))
     
	    (setq lind (cons ind nil))
	    (cond ((not (fixnump (setq *hl (uniq (m- hi low) *uniq-table*))))
		   (setq exp (mevalsumarg exp ind low hi))
		   (return (cons '(%sum) 
				 (list exp ind low hi))))
		  ((equal *hl -1) (return 0))
		  ((signp l *hl)
		   (if $sumhack
		       (return
			(m- (dosum exp ind (m+ 1 hi) (m- low 1) t)))
		     (merror "lower bound to ~:m: ~m~%is greater than the upper bound: sum"
			     low hi))))
	(setq l*i (list low))
	
	(setq u    (make-hash-table :test #'eq :size 
				    (max 8 
					 (truncate
					  (+ 1 hi (- low)) 0.7))))
	;; aim at 70%
	(setq *i low)
	(loop;;until return
	  ;; (format t "*i= ~s~%" *i)
	  ;;put all the terms into the hashtable u.
	  (convert-to-coeff-form   (mbinding (lind l*i) (meval exp))
				   u)
	  
	  ;;termination
	  (if (equal *i hi) (return u))
	  (setf (car l*i) (setf *i (if (numberp *i)(1+ *i)(m+ *i 1))))
	     )				; end loop
	;;	(format t "~% end of loop in dosum-sum")
	(forget (list '(mgeqp) ind low))
	(if (not (eq hi '$inf)) (forget (list '(mgeqp) hi ind)))
	
	(return (hash-to-sorted-list u '(mplus simp))))))


;;(defun redogr()(load  (compile-file "c:/lisp/mzsimpfast.lisp")))


;;; new test

#|
m(i):=remainder(i,13)*z^remainder(i,991)$
sum(m(i),i,1,20000)$


time on Maxima in ACL 9 with normal simp file seems to be:
Evaluation took 35.1720 seconds (36.6720 elapsed) including GC time 0.438 s, using 19601412 cons-cells and 1925976 other bytes.
compiling with (speed 3), 
Evaluation took 15.6090 seconds (16.1410 elapsed) including GC time 0.125 s, using 19601434 cons-cells and 1922120 other bytes.

time on Maxima in ACL 9 with normal simp file with just ALIKE1 optimized:
Evaluation took 31.5780 seconds (32.4690 elapsed) including GC time 0.156 s, using 19601441 cons-cells and 1922984 other bytes.

with programs in this file, time is about 1.1 sec
Evaluation took 1.0940 seconds (1.1400 elapsed) including GC time 0.016 s, using 810644 cons-cells and 2317520 other bytes.

time on commercial macsyma is about 16.8 seconds
Time= 16828 msecs (including 3314 msecs in GC)

time on Maxima 5.25.1 in GCL
Evaluation took 11.1700 seconds (11.1700 elapsed)


time on Maxima 5.25.1 in GCL after loading in simpfast
Evaluation took 2.9200 seconds (2.9200 elapsed)

making z: rat(z) means the the sum takes about 4.2 secs. without simpfast.

Mathematica 8 seems to do the job in about 0.234 Sec.
Timing[Sum[m[i], {i, 1, 20000}];]
OOF.

hm. seems like GCL is 1.5X faster than ACL 9. Maybe compiler optimization settings?

hm. compiling regular simp.lisp with optimize (speed 3) (safety 0)
makes it faster.  ACL 9 speed is
Evaluation took 15.6090 seconds (16.1410 elapsed) including GC time 0.125 s, using 19601434 cons-cells and 1922120 other bytes.

with simpfast,

Evaluation took 0.9530 seconds (1.0000 elapsed) including GC time 0.015 s, using 810582 cons-cells and 2689560 other bytes.
again..
Evaluation took 1.0310 seconds (1.0780 elapsed) including GC time 0.015 s, using 840570 cons-cells and 2842888 other bytes.
again..
Evaluation took 0.9380 seconds (0.9380 elapsed) including GC time 0.016 s, using 810583 cons-cells and 2690008 other bytes.

;;;(maphash #'(lambda(x y)(print (list x y))) *great-hash*)
;;;(maphash #'(lambda(x y)(print x)) *uniq-table*)
 
|#