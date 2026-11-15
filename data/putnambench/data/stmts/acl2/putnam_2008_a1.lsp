;; Statement-only formalization of PutnamBench artifact putnam_2008_a1:
;; a function with zero cyclic three-term sums is a difference of values of
;; a unary function. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; F is an arbitrary function on an arbitrary strict ordered field. The
;; source existential function has the explicit witness g(x) = f(x, 0);
;; stating that this witness works is equivalent to the existential
;; conclusion under the cyclic-sum hypothesis.
(defstub p2008a1-carrier (x) t)
(defstub p2008a1-add-op (x y) t)
(defstub p2008a1-multiply-op (x y) t)
(defstub p2008a1-negate-op (x) t)
(defstub p2008a1-less-op (x y) t)
(defstub p2008a1-f (x y) t)

(defun p2008a1-member-p (x)
  (if (p2008a1-carrier x) t nil))

(defun p2008a1-add (x y)
  (p2008a1-add-op x y))

(defun p2008a1-mul (x y)
  (p2008a1-multiply-op x y))

(defun p2008a1-neg (x)
  (p2008a1-negate-op x))

(defun p2008a1-sub (x y)
  (p2008a1-add x (p2008a1-neg y)))

(defun p2008a1-less (x y)
  (if (p2008a1-less-op x y) t nil))

(defun-sk p2008a1-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p2008a1-member-p x)
      (p2008a1-member-p y)
      (p2008a1-member-p z))
     (and
      (p2008a1-member-p (p2008a1-add x y))
      (p2008a1-member-p (p2008a1-mul x y))
      (p2008a1-member-p (p2008a1-neg x))
      (equal (p2008a1-add (p2008a1-add x y) z)
             (p2008a1-add x (p2008a1-add y z)))
      (equal (p2008a1-add x y)
             (p2008a1-add y x))
      (equal (p2008a1-add x zero) x)
      (equal (p2008a1-add x (p2008a1-neg x)) zero)
      (equal (p2008a1-mul (p2008a1-mul x y) z)
             (p2008a1-mul x (p2008a1-mul y z)))
      (equal (p2008a1-mul x y)
             (p2008a1-mul y x))
      (equal (p2008a1-mul x one) x)
      (equal
       (p2008a1-mul x (p2008a1-add y z))
       (p2008a1-add (p2008a1-mul x y)
                    (p2008a1-mul x z)))))))

(defun-sk p2008a1-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p2008a1-member-p x)
      (p2008a1-member-p y)
      (p2008a1-member-p z))
     (and
      (not (p2008a1-less x x))
      (or (equal x y)
          (p2008a1-less x y)
          (p2008a1-less y x))
      (implies
       (and (p2008a1-less x y)
            (p2008a1-less y z))
       (p2008a1-less x z))
      (implies
       (p2008a1-less x y)
       (p2008a1-less (p2008a1-add x z)
                     (p2008a1-add y z)))
      (implies
       (and (p2008a1-less zero x)
            (p2008a1-less zero y))
       (p2008a1-less zero (p2008a1-mul x y)))))))

(defun p2008a1-ordered-ring-p (zero one)
  (and
   (p2008a1-member-p zero)
   (p2008a1-member-p one)
   (not (equal zero one))
   (p2008a1-less zero one)
   (p2008a1-ring-laws-p zero one)
   (p2008a1-order-laws-p zero)))

(defun-sk p2008a1-function-p ()
  (forall (x y)
    (implies
     (and (p2008a1-member-p x)
          (p2008a1-member-p y))
     (p2008a1-member-p (p2008a1-f x y)))))

(defun-sk p2008a1-cyclic-sum-p (zero)
  (forall (x y z)
    (implies
     (and
      (p2008a1-member-p x)
      (p2008a1-member-p y)
      (p2008a1-member-p z))
     (equal
      (p2008a1-add
       (p2008a1-add (p2008a1-f x y)
                    (p2008a1-f y z))
       (p2008a1-f z x))
      zero))))

(defun p2008a1-g (zero x)
  (p2008a1-f x zero))

(defun-sk p2008a1-canonical-witness-works-p (zero)
  (forall (x y)
    (implies
     (and (p2008a1-member-p x)
          (p2008a1-member-p y))
     (equal
      (p2008a1-f x y)
      (p2008a1-sub
       (p2008a1-g zero x)
       (p2008a1-g zero y))))))

(defun putnambench-putnam-2008-a1-statement (zero one)
  (implies
   (and
    (p2008a1-ordered-ring-p zero one)
    (p2008a1-function-p)
    (p2008a1-cyclic-sum-p zero))
   (p2008a1-canonical-witness-works-p zero)))

(value-triple :itpeval-statement-checked)
:q
