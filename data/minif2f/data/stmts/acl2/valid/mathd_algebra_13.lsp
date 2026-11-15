;; Statement-only formalization of miniF2F artifact mathd_algebra_13:
;; a partial-fraction identity over every admissible real x uniquely
;; determines its coefficients a=-6 and b=10. This file contains no proof.
;;
;; ACL2 has no native real field. The arbitrary characteristic-zero field
;; carrier preserves a, b, the universally quantified x, both denominator
;; side conditions, and the source identity directly. Every law is an
;; explicit premise; no coefficient-solving shortcut replaces the identity.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd13-real-p (value) t)
(defstub mathd13-zero () t)
(defstub mathd13-one () t)
(defstub mathd13-add (left right) t)
(defstub mathd13-mul (left right) t)
(defstub mathd13-neg (value) t)
(defstub mathd13-inv (value) t)
(defstub mathd13-of-rational (value) t)

(defun mathd13-sub (left right)
  (mathd13-add left (mathd13-neg right)))

(defun mathd13-div (left right)
  (mathd13-mul left (mathd13-inv right)))

(defun mathd13-pow2 (value)
  (mathd13-mul value value))

(defun-sk mathd13-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd13-real-p x)
          (mathd13-real-p y))
     (and
      (mathd13-real-p (mathd13-add x y))
      (mathd13-real-p (mathd13-mul x y))))
    (implies
     (mathd13-real-p x)
     (and
      (mathd13-real-p (mathd13-neg x))
      (mathd13-real-p (mathd13-inv x))))
    (implies
     (and
      (mathd13-real-p x)
      (mathd13-real-p y)
      (mathd13-real-p z))
     (equal
      (mathd13-add (mathd13-add x y) z)
      (mathd13-add x (mathd13-add y z))))
    (implies
     (and (mathd13-real-p x)
          (mathd13-real-p y))
     (equal (mathd13-add x y)
            (mathd13-add y x)))
    (implies
     (mathd13-real-p x)
     (and
      (equal (mathd13-add x (mathd13-zero)) x)
      (equal
       (mathd13-add x (mathd13-neg x))
       (mathd13-zero))))
    (implies
     (and
      (mathd13-real-p x)
      (mathd13-real-p y)
      (mathd13-real-p z))
     (equal
      (mathd13-mul (mathd13-mul x y) z)
      (mathd13-mul x (mathd13-mul y z))))
    (implies
     (and (mathd13-real-p x)
          (mathd13-real-p y))
     (equal (mathd13-mul x y)
            (mathd13-mul y x)))
    (implies
     (mathd13-real-p x)
     (equal (mathd13-mul x (mathd13-one)) x))
    (implies
     (and
      (mathd13-real-p x)
      (not (equal x (mathd13-zero))))
     (equal
      (mathd13-mul x (mathd13-inv x))
      (mathd13-one)))
    (equal (mathd13-inv (mathd13-zero))
           (mathd13-zero))
    (implies
     (and
      (mathd13-real-p x)
      (mathd13-real-p y)
      (mathd13-real-p z))
     (equal
      (mathd13-mul x (mathd13-add y z))
      (mathd13-add
       (mathd13-mul x y)
       (mathd13-mul x z)))))))

(defun-sk mathd13-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd13-real-p (mathd13-of-rational p))
     (equal (mathd13-of-rational 0)
            (mathd13-zero))
     (equal (mathd13-of-rational 1)
            (mathd13-one))
     (equal
      (mathd13-of-rational (+ p q))
      (mathd13-add
       (mathd13-of-rational p)
       (mathd13-of-rational q)))
     (equal
      (mathd13-of-rational (* p q))
      (mathd13-mul
       (mathd13-of-rational p)
       (mathd13-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd13-of-rational p)
       (mathd13-of-rational q)))))))

(defun mathd13-real-field-p ()
  (and
   (mathd13-real-p (mathd13-zero))
   (mathd13-real-p (mathd13-one))
   (not (equal (mathd13-zero) (mathd13-one)))
   (mathd13-field-laws-p)
   (mathd13-rational-laws-p)))

(defun-sk mathd13-partial-fraction-identity-p (a b)
  (forall
   (x)
   (implies
    (and
     (mathd13-real-p x)
     (not
      (equal
       (mathd13-sub x (mathd13-of-rational 3))
       (mathd13-zero)))
     (not
      (equal
       (mathd13-sub x (mathd13-of-rational 5))
       (mathd13-zero))))
    (equal
     (mathd13-div
      (mathd13-mul
       (mathd13-of-rational 4)
       x)
      (mathd13-add
       (mathd13-sub
        (mathd13-pow2 x)
        (mathd13-mul
         (mathd13-of-rational 8)
         x))
       (mathd13-of-rational 15)))
     (mathd13-add
      (mathd13-div
       a
       (mathd13-sub x (mathd13-of-rational 3)))
      (mathd13-div
       b
       (mathd13-sub x (mathd13-of-rational 5))))))))

(defun-sk mathd-algebra-13-statement-p ()
  (forall
   (a b)
   (implies
    (and
     (mathd13-real-field-p)
     (mathd13-real-p a)
     (mathd13-real-p b)
     (mathd13-partial-fraction-identity-p a b))
    (and
     (equal a (mathd13-of-rational -6))
     (equal b (mathd13-of-rational 10))))))

(value-triple :itpeval-statement-checked)
:q
