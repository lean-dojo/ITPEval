;; Statement-only formalization of miniF2F artifact mathd_algebra_89:
;; for every nonzero real b, (7*b^3)^2 * (4*b^2)^(-3) is equal to 49/64.
;; This file contains no proof.
;;
;; ACL2 has no native real field. The arbitrary characteristic-zero field
;; carrier below preserves the source variable, powers, inverse, and rational
;; constant directly. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd89-real-p (value) t)
(defstub mathd89-zero () t)
(defstub mathd89-one () t)
(defstub mathd89-add (left right) t)
(defstub mathd89-mul (left right) t)
(defstub mathd89-neg (value) t)
(defstub mathd89-inv (value) t)
(defstub mathd89-of-rational (value) t)

(defun mathd89-pow2 (value)
  (mathd89-mul value value))

(defun mathd89-pow3 (value)
  (mathd89-mul (mathd89-pow2 value) value))

(defun-sk mathd89-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd89-real-p x)
          (mathd89-real-p y))
     (and
      (mathd89-real-p (mathd89-add x y))
      (mathd89-real-p (mathd89-mul x y))))
    (implies
     (mathd89-real-p x)
     (and
      (mathd89-real-p (mathd89-neg x))
      (mathd89-real-p (mathd89-inv x))))
    (implies
     (and
      (mathd89-real-p x)
      (mathd89-real-p y)
      (mathd89-real-p z))
     (equal
      (mathd89-add (mathd89-add x y) z)
      (mathd89-add x (mathd89-add y z))))
    (implies
     (and (mathd89-real-p x)
          (mathd89-real-p y))
     (equal (mathd89-add x y)
            (mathd89-add y x)))
    (implies
     (mathd89-real-p x)
     (and
      (equal (mathd89-add x (mathd89-zero)) x)
      (equal
       (mathd89-add x (mathd89-neg x))
       (mathd89-zero))))
    (implies
     (and
      (mathd89-real-p x)
      (mathd89-real-p y)
      (mathd89-real-p z))
     (equal
      (mathd89-mul (mathd89-mul x y) z)
      (mathd89-mul x (mathd89-mul y z))))
    (implies
     (and (mathd89-real-p x)
          (mathd89-real-p y))
     (equal (mathd89-mul x y)
            (mathd89-mul y x)))
    (implies
     (mathd89-real-p x)
     (equal (mathd89-mul x (mathd89-one)) x))
    (implies
     (and
      (mathd89-real-p x)
      (not (equal x (mathd89-zero))))
     (equal
      (mathd89-mul x (mathd89-inv x))
      (mathd89-one)))
    (equal (mathd89-inv (mathd89-zero))
           (mathd89-zero))
    (implies
     (and
      (mathd89-real-p x)
      (mathd89-real-p y)
      (mathd89-real-p z))
     (equal
      (mathd89-mul x (mathd89-add y z))
      (mathd89-add
       (mathd89-mul x y)
       (mathd89-mul x z)))))))

(defun-sk mathd89-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd89-real-p (mathd89-of-rational p))
     (equal (mathd89-of-rational 0)
            (mathd89-zero))
     (equal (mathd89-of-rational 1)
            (mathd89-one))
     (equal
      (mathd89-of-rational (+ p q))
      (mathd89-add
       (mathd89-of-rational p)
       (mathd89-of-rational q)))
     (equal
      (mathd89-of-rational (* p q))
      (mathd89-mul
       (mathd89-of-rational p)
       (mathd89-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd89-of-rational p)
       (mathd89-of-rational q)))))))

(defun mathd89-real-field-p ()
  (and
   (mathd89-real-p (mathd89-zero))
   (mathd89-real-p (mathd89-one))
   (not (equal (mathd89-zero) (mathd89-one)))
   (mathd89-field-laws-p)
   (mathd89-rational-laws-p)))

(defun-sk mathd-algebra-89-statement-p ()
  (forall
   (b)
   (implies
    (and
     (mathd89-real-field-p)
     (mathd89-real-p b)
     (not (equal b (mathd89-zero))))
    (equal
     (mathd89-mul
      (mathd89-pow2
       (mathd89-mul
        (mathd89-of-rational 7)
        (mathd89-pow3 b)))
      (mathd89-inv
       (mathd89-pow3
        (mathd89-mul
         (mathd89-of-rational 4)
         (mathd89-pow2 b)))))
     (mathd89-of-rational 49/64)))))

(value-triple :itpeval-statement-checked)
:q
