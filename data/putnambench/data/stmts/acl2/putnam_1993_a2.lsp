;; Statement-only formalization of PutnamBench artifact putnam_1993_a2:
;; a nonzero sequence with constant adjacent determinant has a common
;; second-order recurrence coefficient. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The theorem is algebraic. X is an arbitrary sequence in an arbitrary
;; field, represented by ACL2's conservative generic-symbol mechanism.
(defstub p1993a2-carrier (x) t)
(defstub p1993a2-add-op (x y) t)
(defstub p1993a2-multiply-op (x y) t)
(defstub p1993a2-negate-op (x) t)
(defstub p1993a2-inverse-op (x) t)
(defstub p1993a2-x (n) t)

(defun p1993a2-member-p (x)
  (if (p1993a2-carrier x) t nil))

(defun p1993a2-add (x y)
  (p1993a2-add-op x y))

(defun p1993a2-mul (x y)
  (p1993a2-multiply-op x y))

(defun p1993a2-neg (x)
  (p1993a2-negate-op x))

(defun p1993a2-sub (x y)
  (p1993a2-add x (p1993a2-neg y)))

(defun p1993a2-inv (x)
  (p1993a2-inverse-op x))

(defun-sk p1993a2-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1993a2-member-p x)
      (p1993a2-member-p y)
      (p1993a2-member-p z))
     (and
      (p1993a2-member-p (p1993a2-add x y))
      (p1993a2-member-p (p1993a2-mul x y))
      (p1993a2-member-p (p1993a2-neg x))
      (implies
       (not (equal x zero))
       (p1993a2-member-p (p1993a2-inv x)))
      (equal (p1993a2-add (p1993a2-add x y) z)
             (p1993a2-add x (p1993a2-add y z)))
      (equal (p1993a2-add x y)
             (p1993a2-add y x))
      (equal (p1993a2-add x zero) x)
      (equal (p1993a2-add x (p1993a2-neg x)) zero)
      (equal (p1993a2-mul (p1993a2-mul x y) z)
             (p1993a2-mul x (p1993a2-mul y z)))
      (equal (p1993a2-mul x y)
             (p1993a2-mul y x))
      (equal (p1993a2-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1993a2-mul x (p1993a2-inv x)) one))
      (equal
       (p1993a2-mul x (p1993a2-add y z))
       (p1993a2-add (p1993a2-mul x y)
                    (p1993a2-mul x z)))))))

(defun p1993a2-field-p (zero one)
  (and
   (p1993a2-member-p zero)
   (p1993a2-member-p one)
   (not (equal zero one))
   (p1993a2-field-laws-p zero one)))

(defun-sk p1993a2-sequence-p (zero)
  (forall (n)
    (implies
     (natp n)
     (and
      (p1993a2-member-p (p1993a2-x n))
      (not (equal (p1993a2-x n) zero))))))

(defun-sk p1993a2-determinant-condition-p (one)
  (forall (n)
    (implies
     (and (natp n)
          (<= 1 n))
     (equal
      (p1993a2-sub
       (p1993a2-mul (p1993a2-x n)
                    (p1993a2-x n))
       (p1993a2-mul (p1993a2-x (- n 1))
                    (p1993a2-x (+ n 1))))
      one))))

(defun-sk p1993a2-recurrence-p (coefficient)
  (forall (n)
    (implies
     (and (natp n)
          (<= 1 n))
     (equal
      (p1993a2-x (+ n 1))
      (p1993a2-sub
       (p1993a2-mul coefficient (p1993a2-x n))
       (p1993a2-x (- n 1)))))))

(defun-sk p1993a2-has-coefficient-p ()
  (exists (coefficient)
    (and
     (p1993a2-member-p coefficient)
     (p1993a2-recurrence-p coefficient))))

(defun putnambench-putnam-1993-a2-statement (zero one)
  (implies
   (and
    (p1993a2-field-p zero one)
    (p1993a2-sequence-p zero)
    (p1993a2-determinant-condition-p one))
   (p1993a2-has-coefficient-p)))

(value-triple :itpeval-statement-checked)
:q
