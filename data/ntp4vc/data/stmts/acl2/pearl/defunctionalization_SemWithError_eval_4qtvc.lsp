;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_SemWithError_eval_4qtvc: structural decrease
;; and semantic preservation for direct evaluation of subtraction expressions
;; with underflow through defunctionalized continuations. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions encode exactly the source datatype Cte(integer) | Sub(expr,expr).

(defun swe4-cte (number)
  (list :cte number))

(defun swe4-sub (left right)
  (list :sub left right))

(defun swe4-expr-p (expression)
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
     (swe4-expr-p (cadr expression))
     (swe4-expr-p (caddr expression))))
   (t nil)))

;; Values encode exactly Vnum(integer) | Underflow.

(defun swe4-vnum (number)
  (list :vnum number))

(defun swe4-underflow ()
  :underflow)

(defun swe4-value-p (value)
  (or
   (eq value :underflow)
   (and
    (consp value)
    (eq (car value) :vnum)
    (consp (cdr value))
    (integerp (cadr value))
    (null (cddr value)))))

(defun swe4-vnum-value (value)
  (cadr value))

;; Continuations encode exactly I | A(expr,cont) | B(integer,cont).

(defun swe4-cont-i ()
  :i)

(defun swe4-cont-a (expression continuation)
  (list :a expression continuation))

(defun swe4-cont-b (number continuation)
  (list :b number continuation))

(defun swe4-cont-p (continuation)
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
     (swe4-expr-p (cadr continuation))
     (swe4-cont-p (caddr continuation))))
   ((and
     (consp continuation)
     (eq (car continuation) :b)
     (consp (cdr continuation))
     (consp (cddr continuation))
     (null (cdddr continuation)))
    (and
     (integerp (cadr continuation))
     (swe4-cont-p (caddr continuation))))
   (t nil)))

;; Direct error-aware evaluation of expressions.

(defun swe4-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((eq (car expression) :cte)
    (if (<= 0 (cadr expression))
        (swe4-vnum (cadr expression))
      (swe4-underflow)))
   ((eq (car expression) :sub)
    (let ((left-value (swe4-eval-0 (cadr expression))))
      (if (eq left-value :underflow)
          (swe4-underflow)
        (let ((right-value (swe4-eval-0 (caddr expression))))
          (if (eq right-value :underflow)
              (swe4-underflow)
            (if (<= (swe4-vnum-value right-value)
                    (swe4-vnum-value left-value))
                (swe4-vnum
                 (- (swe4-vnum-value left-value)
                    (swe4-vnum-value right-value)))
              (swe4-underflow)))))))
   (t (swe4-underflow))))

;; The source Defunctionalization.size_e and the local continuation size.

(defun swe4-expr-size (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((eq (car expression) :cte)
    1)
   ((eq (car expression) :sub)
    (+ 3
       (swe4-expr-size (cadr expression))
       (swe4-expr-size (caddr expression))))
   (t 0)))

(defun swe4-cont-size (continuation)
  (declare (xargs :measure (acl2-count continuation)))
  (cond
   ((eq continuation :i)
    0)
   ((eq (car continuation) :a)
    (+ 2
       (swe4-expr-size (cadr continuation))
       (swe4-cont-size (caddr continuation))))
   ((eq (car continuation) :b)
    (+ 1
       (swe4-cont-size (caddr continuation))))
   (t 0)))

;; A finite tagged tree is constructor evidence for the source inductive
;; eval_cont relation. The four tags correspond bijectively to its underflow,
;; a1, a2, and a3 constructors.

(defun swe4-eval-cont-derivation-p
    (derivation continuation input result)
  (declare (xargs :measure (acl2-count derivation)))
  (cond
   ((and
     (consp derivation)
     (eq (car derivation) :underflow))
    (and
     (swe4-cont-p (cdr derivation))
     (equal continuation (cdr derivation))
     (equal input (swe4-underflow))
     (equal result (swe4-underflow))))
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
       (swe4-cont-p tail)
       (swe4-expr-p expression)
       (swe4-value-p rule-result)
       (equal continuation (swe4-cont-a expression tail))
       (equal input (swe4-vnum number))
       (equal result rule-result)
       (swe4-eval-cont-derivation-p
        subderivation
        (swe4-cont-b number tail)
        (swe4-eval-0 expression)
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
       (swe4-cont-p tail)
       (integerp number)
       (integerp first-number)
       (swe4-value-p rule-result)
       (equal continuation (swe4-cont-b first-number tail))
       (equal input (swe4-vnum number))
       (equal result rule-result)
       (swe4-eval-cont-derivation-p
        subderivation
        tail
        (if (<= number first-number)
            (swe4-vnum (- first-number number))
          (swe4-underflow))
        rule-result))))
   ((and
     (consp derivation)
     (eq (car derivation) :a3))
    (let ((number (cdr derivation)))
      (and
       (integerp number)
       (equal continuation (swe4-cont-i))
       (equal input (swe4-vnum number))
       (equal result (swe4-vnum number)))))
   (t nil)))

(defun-sk swe4-eval-cont-p (continuation input result)
  (exists (derivation)
    (swe4-eval-cont-derivation-p
     derivation continuation input result)))

;; Exact expression-constructor split of the source structural size conjunct.

(defun swe4-size-obligation-p (expression continuation)
  (let ((whole-size
         (+ (swe4-cont-size continuation)
            (swe4-expr-size expression))))
    (cond
     ((eq (car expression) :cte)
      (implies
       (<= 0 (cadr expression))
       (and
        (and
         (<= 0 whole-size)
         (< (swe4-cont-size continuation)
            whole-size))
        (<= 0 (cadr expression)))))
     ((eq (car expression) :sub)
      (let ((left (cadr expression))
            (right (caddr expression)))
        (and
         (<= 0 whole-size)
         (< (+ (swe4-cont-size
                (swe4-cont-a right continuation))
               (swe4-expr-size left))
            whole-size))))
     (t nil))))

;; Exact matched premise and conclusion of the result implication.

(defun swe4-result-condition-p
    (expression continuation result)
  (implies
   (cond
    ((eq (car expression) :cte)
     (if (<= 0 (cadr expression))
         (swe4-eval-cont-p
          continuation
          (swe4-vnum (cadr expression))
          result)
       (equal result (swe4-underflow))))
    ((eq (car expression) :sub)
     (swe4-eval-cont-p
      (swe4-cont-a (caddr expression) continuation)
      (swe4-eval-0 (cadr expression))
      result))
    (t nil))
   (swe4-eval-cont-p
    continuation
    (swe4-eval-0 expression)
    result)))

(defun-sk swe4-all-results-p (expression continuation)
  (forall (result)
    (implies
     (swe4-value-p result)
     (swe4-result-condition-p
      expression continuation result))))

(defun-sk
    ntp4vc-pearl-defunctionalization-semwitherror-eval-4qtvc-statement
    ()
  (forall (expression continuation)
    (implies
     (and
      (swe4-expr-p expression)
      (swe4-cont-p continuation))
     (and
      (swe4-size-obligation-p expression continuation)
      (swe4-all-results-p expression continuation)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
