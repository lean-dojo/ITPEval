;; Statement-only formalization of miniF2F artifact algebra_9onxpypzleqsum2onxpy:
;; for positive reals x, y, and z,
;;   9/(x+y+z) <= 2/(x+y) + 2/(y+z) + 2/(z+x).
;; This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, and order below present an Archimedean
;; ordered field. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub alg9sum-real-p (value) t)
(defstub alg9sum-zero () t)
(defstub alg9sum-one () t)
(defstub alg9sum-add (left right) t)
(defstub alg9sum-mul (left right) t)
(defstub alg9sum-neg (value) t)
(defstub alg9sum-inv (value) t)
(defstub alg9sum-lt (left right) t)
(defstub alg9sum-of-rational (value) t)

(defun alg9sum-div (left right)
  (alg9sum-mul left (alg9sum-inv right)))

(defun alg9sum-le (left right)
  (or (alg9sum-lt left right)
      (equal left right)))

(defun alg9sum-abs (value)
  (if (alg9sum-lt value (alg9sum-zero))
      (alg9sum-neg value)
    value))

(defun alg9sum-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (alg9sum-zero)
    (alg9sum-add
     (alg9sum-one)
     (alg9sum-natural (1- n)))))

(defun-sk alg9sum-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (alg9sum-real-p x)
          (alg9sum-real-p y))
     (and
      (alg9sum-real-p (alg9sum-add x y))
      (alg9sum-real-p (alg9sum-mul x y))))
    (implies
     (alg9sum-real-p x)
     (and
      (alg9sum-real-p (alg9sum-neg x))
      (alg9sum-real-p (alg9sum-inv x))))

    ;; Additive commutative group.
    (implies
     (and
      (alg9sum-real-p x)
      (alg9sum-real-p y)
      (alg9sum-real-p z))
     (equal
      (alg9sum-add (alg9sum-add x y) z)
      (alg9sum-add x (alg9sum-add y z))))
    (implies
     (and (alg9sum-real-p x)
          (alg9sum-real-p y))
     (equal (alg9sum-add x y)
            (alg9sum-add y x)))
    (implies
     (alg9sum-real-p x)
     (and
      (equal (alg9sum-add x (alg9sum-zero)) x)
      (equal
       (alg9sum-add x (alg9sum-neg x))
       (alg9sum-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and
      (alg9sum-real-p x)
      (alg9sum-real-p y)
      (alg9sum-real-p z))
     (equal
      (alg9sum-mul (alg9sum-mul x y) z)
      (alg9sum-mul x (alg9sum-mul y z))))
    (implies
     (and (alg9sum-real-p x)
          (alg9sum-real-p y))
     (equal (alg9sum-mul x y)
            (alg9sum-mul y x)))
    (implies
     (alg9sum-real-p x)
     (equal (alg9sum-mul x (alg9sum-one)) x))
    (implies
     (and
      (alg9sum-real-p x)
      (not (equal x (alg9sum-zero))))
     (equal
      (alg9sum-mul x (alg9sum-inv x))
      (alg9sum-one)))
    (equal (alg9sum-inv (alg9sum-zero))
           (alg9sum-zero))

    ;; Distributivity.
    (implies
     (and
      (alg9sum-real-p x)
      (alg9sum-real-p y)
      (alg9sum-real-p z))
     (equal
      (alg9sum-mul x (alg9sum-add y z))
      (alg9sum-add
       (alg9sum-mul x y)
       (alg9sum-mul x z)))))))

(defun-sk alg9sum-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (alg9sum-real-p x)
     (not (alg9sum-lt x x)))
    (implies
     (and (alg9sum-real-p x)
          (alg9sum-real-p y))
     (or (alg9sum-lt x y)
         (equal x y)
         (alg9sum-lt y x)))
    (implies
     (and
      (alg9sum-real-p x)
      (alg9sum-real-p y)
      (alg9sum-real-p z)
      (alg9sum-lt x y)
      (alg9sum-lt y z))
     (alg9sum-lt x z))

    ;; Compatibility with addition and positive multiplication.
    (implies
     (and
      (alg9sum-real-p x)
      (alg9sum-real-p y)
      (alg9sum-real-p z))
     (iff
      (alg9sum-lt x y)
      (alg9sum-lt
       (alg9sum-add x z)
       (alg9sum-add y z))))
    (implies
     (and
      (alg9sum-real-p x)
      (alg9sum-real-p y)
      (alg9sum-lt (alg9sum-zero) x)
      (alg9sum-lt (alg9sum-zero) y))
     (alg9sum-lt
      (alg9sum-zero)
      (alg9sum-mul x y))))))

(defun-sk alg9sum-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (alg9sum-real-p (alg9sum-of-rational p))
     (equal (alg9sum-of-rational 0)
            (alg9sum-zero))
     (equal (alg9sum-of-rational 1)
            (alg9sum-one))
     (equal
      (alg9sum-of-rational (+ p q))
      (alg9sum-add
       (alg9sum-of-rational p)
       (alg9sum-of-rational q)))
     (equal
      (alg9sum-of-rational (* p q))
      (alg9sum-mul
       (alg9sum-of-rational p)
       (alg9sum-of-rational q)))
     (iff
      (equal p q)
      (equal
       (alg9sum-of-rational p)
       (alg9sum-of-rational q)))
     (iff
      (< p q)
      (alg9sum-lt
       (alg9sum-of-rational p)
       (alg9sum-of-rational q)))))))

(defun-sk alg9sum-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (alg9sum-lt x (alg9sum-natural n)))))

(defun-sk alg9sum-archimedean-p ()
  (forall
   (x)
   (implies
    (alg9sum-real-p x)
    (alg9sum-natural-bound-exists-p x))))

(defun alg9sum-real-field-p ()
  (and
   (alg9sum-real-p (alg9sum-zero))
   (alg9sum-real-p (alg9sum-one))
   (not (equal (alg9sum-zero) (alg9sum-one)))
   (alg9sum-lt (alg9sum-zero) (alg9sum-one))
   (alg9sum-field-laws-p)
   (alg9sum-order-laws-p)
   (alg9sum-rational-laws-p)
   (alg9sum-archimedean-p)))

(defun-sk algebra-9onxpypzleqsum2onxpy-statement-p ()
  (forall
   (x y z)
   (implies
    (and
     (alg9sum-real-field-p)
     (alg9sum-real-p x)
     (alg9sum-real-p y)
     (alg9sum-real-p z)
     (alg9sum-lt (alg9sum-zero) x)
     (alg9sum-lt (alg9sum-zero) y)
     (alg9sum-lt (alg9sum-zero) z))
    (alg9sum-le
     (alg9sum-div
      (alg9sum-of-rational 9)
      (alg9sum-add (alg9sum-add x y) z))
     (alg9sum-add
      (alg9sum-add
       (alg9sum-div
        (alg9sum-of-rational 2)
        (alg9sum-add x y))
       (alg9sum-div
        (alg9sum-of-rational 2)
        (alg9sum-add y z)))
      (alg9sum-div
       (alg9sum-of-rational 2)
       (alg9sum-add z x)))))))

(value-triple :itpeval-statement-checked)
:q
