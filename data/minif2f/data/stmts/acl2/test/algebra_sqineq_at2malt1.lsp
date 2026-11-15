;; Statement-only formalization of miniF2F artifact
;; algebra_sqineq_at2malt1: for every real a, a*(2-a) is at most 1.
;; This file contains no proof.
;;
;; ACL2 has no native real field. The explicit ordered-field carrier below
;; preserves the arbitrary source variable and polynomial inequality directly.
;; The theorem is algebraic and valid in every ordered field, including the
;; reals. Every structural law is a premise; none assumes the conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub sqat2-real-p (value) t)
(defstub sqat2-zero () t)
(defstub sqat2-one () t)
(defstub sqat2-add (left right) t)
(defstub sqat2-mul (left right) t)
(defstub sqat2-neg (value) t)
(defstub sqat2-lt (left right) t)
(defstub sqat2-of-rational (value) t)

(defun sqat2-sub (left right)
  (sqat2-add left (sqat2-neg right)))

(defun sqat2-le (left right)
  (or (sqat2-lt left right)
      (equal left right)))

(defun-sk sqat2-ring-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (sqat2-real-p x)
          (sqat2-real-p y))
     (and
      (sqat2-real-p (sqat2-add x y))
      (sqat2-real-p (sqat2-mul x y))))
    (implies
     (sqat2-real-p x)
     (sqat2-real-p (sqat2-neg x)))
    (implies
     (and
      (sqat2-real-p x)
      (sqat2-real-p y)
      (sqat2-real-p z))
     (equal
      (sqat2-add (sqat2-add x y) z)
      (sqat2-add x (sqat2-add y z))))
    (implies
     (and (sqat2-real-p x)
          (sqat2-real-p y))
     (equal (sqat2-add x y)
            (sqat2-add y x)))
    (implies
     (sqat2-real-p x)
     (and
      (equal (sqat2-add x (sqat2-zero)) x)
      (equal
       (sqat2-add x (sqat2-neg x))
       (sqat2-zero))))
    (implies
     (and
      (sqat2-real-p x)
      (sqat2-real-p y)
      (sqat2-real-p z))
     (equal
      (sqat2-mul (sqat2-mul x y) z)
      (sqat2-mul x (sqat2-mul y z))))
    (implies
     (and (sqat2-real-p x)
          (sqat2-real-p y))
     (equal (sqat2-mul x y)
            (sqat2-mul y x)))
    (implies
     (sqat2-real-p x)
     (equal (sqat2-mul x (sqat2-one)) x))
    (implies
     (and
      (sqat2-real-p x)
      (sqat2-real-p y)
      (sqat2-real-p z))
     (equal
      (sqat2-mul x (sqat2-add y z))
      (sqat2-add
       (sqat2-mul x y)
       (sqat2-mul x z)))))))

(defun-sk sqat2-order-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (sqat2-real-p x)
     (not (sqat2-lt x x)))
    (implies
     (and (sqat2-real-p x)
          (sqat2-real-p y))
     (or (sqat2-lt x y)
         (equal x y)
         (sqat2-lt y x)))
    (implies
     (and
      (sqat2-real-p x)
      (sqat2-real-p y)
      (sqat2-real-p z)
      (sqat2-lt x y)
      (sqat2-lt y z))
     (sqat2-lt x z))
    (implies
     (and
      (sqat2-real-p x)
      (sqat2-real-p y)
      (sqat2-real-p z))
     (iff
      (sqat2-lt x y)
      (sqat2-lt
       (sqat2-add x z)
       (sqat2-add y z))))
    (implies
     (and
      (sqat2-real-p x)
      (sqat2-real-p y)
      (sqat2-lt (sqat2-zero) x)
      (sqat2-lt (sqat2-zero) y))
     (sqat2-lt
      (sqat2-zero)
      (sqat2-mul x y))))))

(defun-sk sqat2-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (sqat2-real-p (sqat2-of-rational p))
     (equal (sqat2-of-rational 0)
            (sqat2-zero))
     (equal (sqat2-of-rational 1)
            (sqat2-one))
     (equal
      (sqat2-of-rational (+ p q))
      (sqat2-add
       (sqat2-of-rational p)
       (sqat2-of-rational q)))
     (equal
      (sqat2-of-rational (* p q))
      (sqat2-mul
       (sqat2-of-rational p)
       (sqat2-of-rational q)))
     (iff
      (equal p q)
      (equal
       (sqat2-of-rational p)
       (sqat2-of-rational q)))
     (iff
      (< p q)
      (sqat2-lt
       (sqat2-of-rational p)
       (sqat2-of-rational q)))))))

(defun sqat2-ordered-field-p ()
  (and
   (sqat2-real-p (sqat2-zero))
   (sqat2-real-p (sqat2-one))
   (not (equal (sqat2-zero) (sqat2-one)))
   (sqat2-lt (sqat2-zero) (sqat2-one))
   (sqat2-ring-laws-p)
   (sqat2-order-laws-p)
   (sqat2-rational-laws-p)))

(defun-sk algebra-sqineq-at2malt1-statement-p ()
  (forall
   (a)
   (implies
    (and
     (sqat2-ordered-field-p)
     (sqat2-real-p a))
    (sqat2-le
     (sqat2-mul
      a
      (sqat2-sub
       (sqat2-of-rational 2)
       a))
     (sqat2-of-rational 1)))))

(value-triple :itpeval-statement-checked)
:q
