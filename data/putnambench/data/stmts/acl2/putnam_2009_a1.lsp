;; Statement-only formalization of PutnamBench artifact putnam_2009_a1:
;; if the values of a plane function sum to zero on every nondegenerate
;; square, then the function is identically zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Coordinates and values lie in an arbitrary strict ordered field, and F is
;; an arbitrary conservative binary function symbol. The theorem's proof is
;; algebraic; no completeness or Cauchy-name representation is required.
(defstub p2009a1-carrier (x) t)
(defstub p2009a1-add-op (x y) t)
(defstub p2009a1-multiply-op (x y) t)
(defstub p2009a1-negate-op (x) t)
(defstub p2009a1-less-op (x y) t)
(defstub p2009a1-f (x y) t)

(defun p2009a1-member-p (x)
  (if (p2009a1-carrier x) t nil))

(defun p2009a1-add (x y)
  (p2009a1-add-op x y))

(defun p2009a1-mul (x y)
  (p2009a1-multiply-op x y))

(defun p2009a1-neg (x)
  (p2009a1-negate-op x))

(defun p2009a1-sub (x y)
  (p2009a1-add x (p2009a1-neg y)))

(defun p2009a1-less (x y)
  (if (p2009a1-less-op x y) t nil))

(defun-sk p2009a1-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p2009a1-member-p x)
      (p2009a1-member-p y)
      (p2009a1-member-p z))
     (and
      (p2009a1-member-p (p2009a1-add x y))
      (p2009a1-member-p (p2009a1-mul x y))
      (p2009a1-member-p (p2009a1-neg x))
      (equal (p2009a1-add (p2009a1-add x y) z)
             (p2009a1-add x (p2009a1-add y z)))
      (equal (p2009a1-add x y)
             (p2009a1-add y x))
      (equal (p2009a1-add x zero) x)
      (equal (p2009a1-add x (p2009a1-neg x)) zero)
      (equal (p2009a1-mul (p2009a1-mul x y) z)
             (p2009a1-mul x (p2009a1-mul y z)))
      (equal (p2009a1-mul x y)
             (p2009a1-mul y x))
      (equal (p2009a1-mul x one) x)
      (equal
       (p2009a1-mul x (p2009a1-add y z))
       (p2009a1-add (p2009a1-mul x y)
                    (p2009a1-mul x z)))))))

(defun-sk p2009a1-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p2009a1-member-p x)
      (p2009a1-member-p y)
      (p2009a1-member-p z))
     (and
      (not (p2009a1-less x x))
      (or (equal x y)
          (p2009a1-less x y)
          (p2009a1-less y x))
      (implies
       (and (p2009a1-less x y)
            (p2009a1-less y z))
       (p2009a1-less x z))
      (implies
       (p2009a1-less x y)
       (p2009a1-less (p2009a1-add x z)
                     (p2009a1-add y z)))
      (implies
       (and (p2009a1-less zero x)
            (p2009a1-less zero y))
       (p2009a1-less zero (p2009a1-mul x y)))))))

(defun p2009a1-ordered-ring-p (zero one)
  (and
   (p2009a1-member-p zero)
   (p2009a1-member-p one)
   (not (equal zero one))
   (p2009a1-less zero one)
   (p2009a1-ring-laws-p zero one)
   (p2009a1-order-laws-p zero)))

(defun-sk p2009a1-function-p ()
  (forall (x y)
    (implies
     (and (p2009a1-member-p x)
          (p2009a1-member-p y))
     (p2009a1-member-p (p2009a1-f x y)))))

(defun p2009a1-zero-vector-p (zero x y)
  (and (equal x zero)
       (equal y zero)))

(defun-sk p2009a1-square-sums-zero-p (zero)
  (forall (origin-x origin-y side-x side-y)
    (implies
     (and
      (p2009a1-member-p origin-x)
      (p2009a1-member-p origin-y)
      (p2009a1-member-p side-x)
      (p2009a1-member-p side-y)
      (not (p2009a1-zero-vector-p zero side-x side-y)))
     (equal
      (p2009a1-add
       (p2009a1-add
        (p2009a1-f origin-x origin-y)
        (p2009a1-f
         (p2009a1-add origin-x side-x)
         (p2009a1-add origin-y side-y)))
       (p2009a1-add
        (p2009a1-f
         (p2009a1-sub
          (p2009a1-add origin-x side-x)
          side-y)
         (p2009a1-add
          (p2009a1-add origin-y side-y)
          side-x))
        (p2009a1-f
         (p2009a1-sub origin-x side-y)
         (p2009a1-add origin-y side-x))))
      zero))))

(defun-sk p2009a1-identically-zero-p (zero)
  (forall (x y)
    (implies
     (and (p2009a1-member-p x)
          (p2009a1-member-p y))
     (equal (p2009a1-f x y) zero))))

(defun putnambench-putnam-2009-a1-statement (zero one)
  (implies
   (and
    (p2009a1-ordered-ring-p zero one)
    (p2009a1-function-p)
    (p2009a1-square-sums-zero-p zero))
   (p2009a1-identically-zero-p zero)))

(value-triple :itpeval-statement-checked)
:q
