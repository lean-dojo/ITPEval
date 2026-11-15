;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_SemWithError_continue_4qtvc: structural
;; decrease and semantic preservation when a nonnegative numeric value
;; continues through a defunctionalized error-aware continuation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions encode exactly the source datatype Cte(integer) | Sub(expr,expr).

(defun dse-cte (number)
  (list :cte number))

(defun dse-sub (left right)
  (list :sub left right))

(defun dse-expr-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((and
     (consp expression)
     (eq (car expression) :cte)
     (consp (cdr expression))
     (null (cddr expression)))
    (integerp (cadr expression)))
   ((and
     (consp expression)
     (eq (car expression) :sub)
     (consp (cdr expression))
     (consp (cddr expression))
     (null (cdddr expression)))
    (and
     (dse-expr-p (cadr expression))
     (dse-expr-p (caddr expression))))
   (t nil)))

;; Values encode exactly Vnum(integer) | Underflow.

(defun dse-vnum (number)
  (list :vnum number))

(defun dse-underflow ()
  :underflow)

(defun dse-value-p (value)
  (or
   (eq value :underflow)
   (and
    (consp value)
    (eq (car value) :vnum)
    (consp (cdr value))
    (integerp (cadr value))
    (null (cddr value)))))

(defun dse-vnum-value (value)
  (cadr value))

;; Continuations encode exactly I | A(expr,cont) | B(integer,cont).

(defun dse-cont-i ()
  :i)

(defun dse-cont-a (expression continuation)
  (list :a expression continuation))

(defun dse-cont-b (number continuation)
  (list :b number continuation))

(defun dse-cont-p (continuation)
  (declare (xargs :measure (acl2-count continuation)))
  (cond
   ((eq continuation :i)
    t)
   ((and
     (consp continuation)
     (eq (car continuation) :a)
     (consp (cdr continuation))
     (consp (cddr continuation))
     (null (cdddr continuation)))
    (and
     (dse-expr-p (cadr continuation))
     (dse-cont-p (caddr continuation))))
   ((and
     (consp continuation)
     (eq (car continuation) :b)
     (consp (cdr continuation))
     (consp (cddr continuation))
     (null (cdddr continuation)))
    (and
     (integerp (cadr continuation))
     (dse-cont-p (caddr continuation))))
   (t nil)))

;; Direct error-aware evaluation of expressions.

(defun dse-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((eq (car expression) :cte)
    (if (<= 0 (cadr expression))
        (dse-vnum (cadr expression))
      (dse-underflow)))
   ((eq (car expression) :sub)
    (let ((left-value (dse-eval-0 (cadr expression))))
      (if (eq left-value :underflow)
          (dse-underflow)
        (let ((right-value (dse-eval-0 (caddr expression))))
          (if (eq right-value :underflow)
              (dse-underflow)
            (if (<= (dse-vnum-value right-value)
                    (dse-vnum-value left-value))
                (dse-vnum
                 (- (dse-vnum-value left-value)
                    (dse-vnum-value right-value)))
              (dse-underflow)))))))
   (t (dse-underflow))))

;; The source Defunctionalization.size_e and the local continuation size.

(defun dse-expr-size (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((eq (car expression) :cte)
    1)
   ((eq (car expression) :sub)
    (+ 3
       (dse-expr-size (cadr expression))
       (dse-expr-size (caddr expression))))
   (t 0)))

(defun dse-cont-size (continuation)
  (declare (xargs :measure (acl2-count continuation)))
  (cond
   ((eq continuation :i)
    0)
   ((eq (car continuation) :a)
    (+ 2
       (dse-expr-size (cadr continuation))
       (dse-cont-size (caddr continuation))))
   ((eq (car continuation) :b)
    (+ 1
       (dse-cont-size (caddr continuation))))
   (t 0)))

;; A finite tagged tree is constructor evidence for the source inductive
;; eval_cont relation.  The four tags below correspond bijectively to its
;; underflow, a1, a2, and a3 constructors.

(defun dse-eval-cont-derivation-p
    (derivation continuation input result)
  (declare (xargs :measure (acl2-count derivation)))
  (cond
   ((and
     (consp derivation)
     (eq (car derivation) :underflow))
    (and
     (dse-cont-p (cdr derivation))
     (equal continuation (cdr derivation))
     (equal input (dse-underflow))
     (equal result (dse-underflow))))
   ((and
     (consp derivation)
     (eq (car derivation) :a1)
     (consp (cdr derivation))
     (consp (cddr derivation))
     (consp (cdddr derivation))
     (consp (cddddr derivation)))
    (let*
        ((number (cadr derivation))
         (tail (caddr derivation))
         (expression (cadddr derivation))
         (rule-result (car (cddddr derivation)))
         (subderivation (cdr (cddddr derivation))))
      (and
       (integerp number)
       (dse-cont-p tail)
       (dse-expr-p expression)
       (dse-value-p rule-result)
       (equal continuation (dse-cont-a expression tail))
       (equal input (dse-vnum number))
       (equal result rule-result)
       (dse-eval-cont-derivation-p
        subderivation
        (dse-cont-b number tail)
        (dse-eval-0 expression)
        rule-result))))
   ((and
     (consp derivation)
     (eq (car derivation) :a2)
     (consp (cdr derivation))
     (consp (cddr derivation))
     (consp (cdddr derivation))
     (consp (cddddr derivation)))
    (let*
        ((tail (cadr derivation))
         (number (caddr derivation))
         (first-number (cadddr derivation))
         (rule-result (car (cddddr derivation)))
         (subderivation (cdr (cddddr derivation))))
      (and
       (dse-cont-p tail)
       (integerp number)
       (integerp first-number)
       (dse-value-p rule-result)
       (equal continuation (dse-cont-b first-number tail))
       (equal input (dse-vnum number))
       (equal result rule-result)
       (dse-eval-cont-derivation-p
        subderivation
        tail
        (if (<= number first-number)
            (dse-vnum (- first-number number))
          (dse-underflow))
        rule-result))))
   ((and
     (consp derivation)
     (eq (car derivation) :a3))
    (let ((number (cdr derivation)))
      (and
       (integerp number)
       (equal continuation (dse-cont-i))
       (equal input (dse-vnum number))
       (equal result (dse-vnum number)))))
   (t nil)))

(defun-sk dse-eval-cont-p (continuation input result)
  (exists (derivation)
    (dse-eval-cont-derivation-p
     derivation continuation input result)))

;; This is the universally quantified second conjunct of continue_4'vc.

(defun-sk dse-result-preservation-p (number continuation)
  (forall (result)
    (implies
     (dse-value-p result)
     (implies
      (cond
       ((eq continuation :i)
        (equal result (dse-vnum number)))
       ((eq (car continuation) :a)
        (let ((expression (cadr continuation))
              (tail (caddr continuation)))
          (dse-eval-cont-p
           (dse-cont-b number tail)
           (dse-eval-0 expression)
           result)))
       ((eq (car continuation) :b)
        (let ((first-number (cadr continuation))
              (tail (caddr continuation)))
          (if (<= number first-number)
              (dse-eval-cont-p
               tail
               (dse-vnum (- first-number number))
               result)
            (equal result (dse-underflow)))))
       (t nil))
      (dse-eval-cont-p
       continuation (dse-vnum number) result)))))

;; The first conjunct is the source case split of structural size facts.

(defun dse-size-case-p (number continuation)
  (cond
   ((eq continuation :i)
    t)
   ((eq (car continuation) :a)
    (let ((expression (cadr continuation))
          (tail (caddr continuation)))
      (and
       (<= 0 (dse-cont-size continuation))
       (< (+ (dse-cont-size (dse-cont-b number tail))
             (dse-expr-size expression))
          (dse-cont-size continuation)))))
   ((eq (car continuation) :b)
    (let ((first-number (cadr continuation))
          (tail (caddr continuation)))
      (implies
       (<= number first-number)
       (and
        (and
         (<= 0 (dse-cont-size continuation))
         (< (dse-cont-size tail)
            (dse-cont-size continuation)))
        (<= 0 (- first-number number))))))
   (t nil)))

(defun-sk
    ntp4vc-defunctionalization-semwitherror-continue-4qtvc-statement ()
  (forall (number continuation)
    (implies
     (and
      (integerp number)
      (dse-cont-p continuation)
      (<= 0 number))
     (and
      (dse-size-case-p number continuation)
      (dse-result-preservation-p number continuation)))))

(value-triple :itpeval-statement-checked)
:q
