;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_Defunctionalization_eval_2qtvc: structural
;; decrease and continuation semantics for a defunctionalized evaluator of
;; integer subtraction expressions. This file contains no proof.

(in-package "ACL2")

;; Expressions are represented bijectively by (:cte . n) and
;; (:sub e1 . e2). Continuations are represented by :i,
;; (:a1 e2 . k), and (:a2 v . k).

(defun ntp4vc-defunctionalization-exprp (e)
  (declare (xargs :measure (acl2-count e)))
  (and
   (consp e)
   (cond
    ((eq (car e) :cte)
     (integerp (cdr e)))
    ((eq (car e) :sub)
     (and
      (consp (cdr e))
      (ntp4vc-defunctionalization-exprp (cadr e))
      (ntp4vc-defunctionalization-exprp (cddr e))))
    (t nil))))

(defun ntp4vc-defunctionalization-contp (c)
  (declare (xargs :measure (acl2-count c)))
  (cond
   ((eq c :i)
    t)
   ((and
     (consp c)
     (eq (car c) :a1)
     (consp (cdr c)))
    (and
     (ntp4vc-defunctionalization-exprp (cadr c))
     (ntp4vc-defunctionalization-contp (cddr c))))
   ((and
     (consp c)
     (eq (car c) :a2)
     (consp (cdr c)))
    (and
     (integerp (cadr c))
     (ntp4vc-defunctionalization-contp (cddr c))))
   (t nil)))

(defun ntp4vc-defunctionalization-a1 (e2 k)
  (cons :a1 (cons e2 k)))

(defun ntp4vc-defunctionalization-eval-expr (e)
  (declare (xargs :measure (acl2-count e)))
  (cond
   ((and
     (consp e)
     (eq (car e) :cte))
    (cdr e))
   ((and
     (consp e)
     (eq (car e) :sub)
     (consp (cdr e)))
    (-
     (ntp4vc-defunctionalization-eval-expr (cadr e))
     (ntp4vc-defunctionalization-eval-expr (cddr e))))
   (t 0)))

(defun ntp4vc-defunctionalization-size-e (e)
  (declare (xargs :measure (acl2-count e)))
  (cond
   ((and
     (consp e)
     (eq (car e) :cte))
    1)
   ((and
     (consp e)
     (eq (car e) :sub)
     (consp (cdr e)))
    (+
     3
     (ntp4vc-defunctionalization-size-e (cadr e))
     (ntp4vc-defunctionalization-size-e (cddr e))))
   (t 0)))

(defun ntp4vc-defunctionalization-size-c (c)
  (declare (xargs :measure (acl2-count c)))
  (cond
   ((eq c :i)
    0)
   ((and
     (consp c)
     (eq (car c) :a1)
     (consp (cdr c)))
    (+
     2
     (ntp4vc-defunctionalization-size-e (cadr c))
     (ntp4vc-defunctionalization-size-c (cddr c))))
   ((and
     (consp c)
     (eq (car c) :a2)
     (consp (cdr c)))
    (+
     1
     (ntp4vc-defunctionalization-size-c (cddr c))))
   (t 0)))

;; This recursive predicate is equivalent to the source inductive relation:
;; each continuation constructor uniquely determines its applicable rule.

(defun ntp4vc-defunctionalization-eval-cont (c value result)
  (declare (xargs :measure (acl2-count c)))
  (cond
   ((eq c :i)
    (equal result value))
   ((and
     (consp c)
     (eq (car c) :a1)
     (consp (cdr c)))
    (ntp4vc-defunctionalization-eval-cont
     (cddr c)
     (-
      value
      (ntp4vc-defunctionalization-eval-expr (cadr c)))
     result))
   ((and
     (consp c)
     (eq (car c) :a2)
     (consp (cdr c)))
    (ntp4vc-defunctionalization-eval-cont
     (cddr c)
     (- (cadr c) value)
     result))
   (t nil)))

(defun ntp4vc-defunctionalization-size-condition (e c)
  (if (eq (car e) :cte)
      (and
       (<=
        0
        (+
         (ntp4vc-defunctionalization-size-c c)
         (ntp4vc-defunctionalization-size-e e)))
       (<
        (ntp4vc-defunctionalization-size-c c)
        (+
         (ntp4vc-defunctionalization-size-c c)
         (ntp4vc-defunctionalization-size-e e))))
    (let ((e1 (cadr e))
          (e2 (cddr e)))
      (and
       (<=
        0
        (+
         (ntp4vc-defunctionalization-size-c c)
         (ntp4vc-defunctionalization-size-e e)))
       (<
        (+
         (ntp4vc-defunctionalization-size-c
          (ntp4vc-defunctionalization-a1 e2 c))
         (ntp4vc-defunctionalization-size-e e1))
        (+
         (ntp4vc-defunctionalization-size-c c)
         (ntp4vc-defunctionalization-size-e e)))))))

(defun ntp4vc-defunctionalization-result-condition
    (e c result)
  (if (eq (car e) :cte)
      (implies
       (ntp4vc-defunctionalization-eval-cont
        c (cdr e) result)
       (ntp4vc-defunctionalization-eval-cont
        c
        (ntp4vc-defunctionalization-eval-expr e)
        result))
    (let ((e1 (cadr e))
          (e2 (cddr e)))
      (implies
       (ntp4vc-defunctionalization-eval-cont
        (ntp4vc-defunctionalization-a1 e2 c)
        (ntp4vc-defunctionalization-eval-expr e1)
        result)
       (ntp4vc-defunctionalization-eval-cont
        c
        (ntp4vc-defunctionalization-eval-expr e)
        result)))))

(defun-sk ntp4vc-defunctionalization-all-results-p (e c)
  (forall (result)
    (implies
     (integerp result)
     (ntp4vc-defunctionalization-result-condition
      e c result))))

(defun ntp4vc-defunctionalization-eval-2qtvc-statement
    (e c)
  (implies
   (and
    (ntp4vc-defunctionalization-exprp e)
    (ntp4vc-defunctionalization-contp c))
   (and
    (ntp4vc-defunctionalization-size-condition e c)
    (ntp4vc-defunctionalization-all-results-p e c))))

(value-triple :itpeval-statement-checked)
:q
