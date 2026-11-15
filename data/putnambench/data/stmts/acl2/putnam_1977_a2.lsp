;; Statement-only formalization of PutnamBench artifact putnam_1977_a2:
;; the nonzero solutions of the reciprocal-sum equations are exactly the
;; three symmetric opposite-pair families. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The problem is purely algebraic. Conservative generic symbols present an
;; arbitrary field, avoiding both a rational-only specialization and APPLY$'s
;; restricted function-object universe.
(defstub p1977a2-carrier (x) t)
(defstub p1977a2-add-op (x y) t)
(defstub p1977a2-multiply-op (x y) t)
(defstub p1977a2-negate-op (x) t)
(defstub p1977a2-inverse-op (x) t)

(defun p1977a2-member-p (x)
  (if (p1977a2-carrier x) t nil))

(defun p1977a2-add (x y)
  (p1977a2-add-op x y))

(defun p1977a2-mul (x y)
  (p1977a2-multiply-op x y))

(defun p1977a2-neg (x)
  (p1977a2-negate-op x))

(defun p1977a2-inv (x)
  (p1977a2-inverse-op x))

(defun-sk p1977a2-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1977a2-member-p x)
      (p1977a2-member-p y)
      (p1977a2-member-p z))
     (and
      (p1977a2-member-p (p1977a2-add x y))
      (p1977a2-member-p (p1977a2-mul x y))
      (p1977a2-member-p (p1977a2-neg x))
      (implies
       (not (equal x zero))
       (p1977a2-member-p (p1977a2-inv x)))
      (equal (p1977a2-add (p1977a2-add x y) z)
             (p1977a2-add x (p1977a2-add y z)))
      (equal (p1977a2-add x y)
             (p1977a2-add y x))
      (equal (p1977a2-add x zero) x)
      (equal (p1977a2-add x (p1977a2-neg x)) zero)
      (equal (p1977a2-mul (p1977a2-mul x y) z)
             (p1977a2-mul x (p1977a2-mul y z)))
      (equal (p1977a2-mul x y)
             (p1977a2-mul y x))
      (equal (p1977a2-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1977a2-mul x (p1977a2-inv x)) one))
      (equal
       (p1977a2-mul x (p1977a2-add y z))
       (p1977a2-add (p1977a2-mul x y)
                    (p1977a2-mul x z)))))))

(defun p1977a2-field-p (zero one)
  (and
   (p1977a2-member-p zero)
   (p1977a2-member-p one)
   (not (equal zero one))
   (p1977a2-field-laws-p zero one)))

(defun p1977a2-equations-p (a b c d)
  (and
   (equal
    (p1977a2-add (p1977a2-add a b) c)
    d)
   (equal
    (p1977a2-add
     (p1977a2-add (p1977a2-inv a)
                  (p1977a2-inv b))
     (p1977a2-inv c))
    (p1977a2-inv d))))

(defun p1977a2-solution-p (a b c d)
  (or
   (and (equal d a)
        (equal b (p1977a2-neg c)))
   (and (equal d b)
        (equal a (p1977a2-neg c)))
   (and (equal d c)
        (equal a (p1977a2-neg b)))))

(defun putnambench-putnam-1977-a2-statement
    (zero one a b c d)
  (implies
   (and
    (p1977a2-field-p zero one)
    (p1977a2-member-p a)
    (p1977a2-member-p b)
    (p1977a2-member-p c)
    (p1977a2-member-p d)
    (not (equal a zero))
    (not (equal b zero))
    (not (equal c zero))
    (not (equal d zero)))
   (iff
    (p1977a2-solution-p a b c d)
    (p1977a2-equations-p a b c d))))

(value-triple :itpeval-statement-checked)
:q
