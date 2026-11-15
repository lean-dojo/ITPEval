;; Statement-only formalization of miniF2F artifact mathd_algebra_441:
;; for every nonzero real x, the displayed product of rational expressions
;; in x is equal to 10. This file contains no proof.
;;
;; ACL2 has no native real field. The arbitrary carrier, operations, and
;; rational embedding below preserve the source quantifier over all reals.
;; Every field law is an explicit premise; DEFSTUB introduces no law, and no
;; premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd441-real-p (value) t)
(defstub mathd441-zero () t)
(defstub mathd441-one () t)
(defstub mathd441-add (left right) t)
(defstub mathd441-mul (left right) t)
(defstub mathd441-neg (value) t)
(defstub mathd441-inv (value) t)
(defstub mathd441-of-rational (value) t)

(defun mathd441-div (left right)
  (mathd441-mul left (mathd441-inv right)))

(defun mathd441-pow2 (value)
  (mathd441-mul value value))

(defun mathd441-pow4 (value)
  (mathd441-pow2 (mathd441-pow2 value)))

(defun-sk mathd441-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (mathd441-real-p x)
          (mathd441-real-p y))
     (and
      (mathd441-real-p (mathd441-add x y))
      (mathd441-real-p (mathd441-mul x y))))
    (implies
     (mathd441-real-p x)
     (and
      (mathd441-real-p (mathd441-neg x))
      (mathd441-real-p (mathd441-inv x))))

    ;; Additive commutative group.
    (implies
     (and
      (mathd441-real-p x)
      (mathd441-real-p y)
      (mathd441-real-p z))
     (equal
      (mathd441-add (mathd441-add x y) z)
      (mathd441-add x (mathd441-add y z))))
    (implies
     (and (mathd441-real-p x)
          (mathd441-real-p y))
     (equal (mathd441-add x y)
            (mathd441-add y x)))
    (implies
     (mathd441-real-p x)
     (and
      (equal (mathd441-add x (mathd441-zero)) x)
      (equal
       (mathd441-add x (mathd441-neg x))
       (mathd441-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and
      (mathd441-real-p x)
      (mathd441-real-p y)
      (mathd441-real-p z))
     (equal
      (mathd441-mul (mathd441-mul x y) z)
      (mathd441-mul x (mathd441-mul y z))))
    (implies
     (and (mathd441-real-p x)
          (mathd441-real-p y))
     (equal (mathd441-mul x y)
            (mathd441-mul y x)))
    (implies
     (mathd441-real-p x)
     (equal (mathd441-mul x (mathd441-one)) x))
    (implies
     (and
      (mathd441-real-p x)
      (not (equal x (mathd441-zero))))
     (equal
      (mathd441-mul x (mathd441-inv x))
      (mathd441-one)))
    (equal (mathd441-inv (mathd441-zero))
           (mathd441-zero))

    ;; Distributivity.
    (implies
     (and
      (mathd441-real-p x)
      (mathd441-real-p y)
      (mathd441-real-p z))
     (equal
      (mathd441-mul x (mathd441-add y z))
      (mathd441-add
       (mathd441-mul x y)
       (mathd441-mul x z)))))))

(defun-sk mathd441-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd441-real-p (mathd441-of-rational p))
     (equal (mathd441-of-rational 0)
            (mathd441-zero))
     (equal (mathd441-of-rational 1)
            (mathd441-one))
     (equal
      (mathd441-of-rational (+ p q))
      (mathd441-add
       (mathd441-of-rational p)
       (mathd441-of-rational q)))
     (equal
      (mathd441-of-rational (* p q))
      (mathd441-mul
       (mathd441-of-rational p)
       (mathd441-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd441-of-rational p)
       (mathd441-of-rational q)))))))

(defun mathd441-real-field-p ()
  (and
   (mathd441-real-p (mathd441-zero))
   (mathd441-real-p (mathd441-one))
   (not (equal (mathd441-zero) (mathd441-one)))
   (mathd441-field-laws-p)
   (mathd441-rational-laws-p)))

(defun-sk mathd-algebra-441-statement-p ()
  (forall
   (x)
   (implies
    (and
     (mathd441-real-field-p)
     (mathd441-real-p x)
     (not (equal x (mathd441-zero))))
    (equal
     (mathd441-mul
      (mathd441-mul
       (mathd441-div
        (mathd441-of-rational 12)
        (mathd441-pow2 x))
       (mathd441-div
        (mathd441-pow4 x)
        (mathd441-mul
         (mathd441-of-rational 14)
         x)))
      (mathd441-div
       (mathd441-of-rational 35)
       (mathd441-mul
        (mathd441-of-rational 3)
        x)))
     (mathd441-of-rational 10)))))

(value-triple :itpeval-statement-checked)
:q
