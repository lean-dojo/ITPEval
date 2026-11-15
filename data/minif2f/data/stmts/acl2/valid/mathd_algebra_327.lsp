;; Statement-only formalization of miniF2F artifact mathd_algebra_327:
;; for every real a, (1/5)*|9+2*a| < 1 implies -7 < a and a < -2.
;; This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, and order below present an Archimedean
;; ordered field. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd327-real-p (value) t)
(defstub mathd327-zero () t)
(defstub mathd327-one () t)
(defstub mathd327-add (left right) t)
(defstub mathd327-mul (left right) t)
(defstub mathd327-neg (value) t)
(defstub mathd327-inv (value) t)
(defstub mathd327-lt (left right) t)
(defstub mathd327-of-rational (value) t)

(defun mathd327-div (left right)
  (mathd327-mul left (mathd327-inv right)))

(defun mathd327-abs (value)
  (if (mathd327-lt value (mathd327-zero))
      (mathd327-neg value)
    value))

(defun mathd327-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd327-zero)
    (mathd327-add
     (mathd327-one)
     (mathd327-natural (1- n)))))

(defun-sk mathd327-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (mathd327-real-p x)
          (mathd327-real-p y))
     (and
      (mathd327-real-p (mathd327-add x y))
      (mathd327-real-p (mathd327-mul x y))))
    (implies
     (mathd327-real-p x)
     (and
      (mathd327-real-p (mathd327-neg x))
      (mathd327-real-p (mathd327-inv x))))

    ;; Additive commutative group.
    (implies
     (and
      (mathd327-real-p x)
      (mathd327-real-p y)
      (mathd327-real-p z))
     (equal
      (mathd327-add (mathd327-add x y) z)
      (mathd327-add x (mathd327-add y z))))
    (implies
     (and (mathd327-real-p x)
          (mathd327-real-p y))
     (equal (mathd327-add x y)
            (mathd327-add y x)))
    (implies
     (mathd327-real-p x)
     (and
      (equal (mathd327-add x (mathd327-zero)) x)
      (equal
       (mathd327-add x (mathd327-neg x))
       (mathd327-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and
      (mathd327-real-p x)
      (mathd327-real-p y)
      (mathd327-real-p z))
     (equal
      (mathd327-mul (mathd327-mul x y) z)
      (mathd327-mul x (mathd327-mul y z))))
    (implies
     (and (mathd327-real-p x)
          (mathd327-real-p y))
     (equal (mathd327-mul x y)
            (mathd327-mul y x)))
    (implies
     (mathd327-real-p x)
     (equal (mathd327-mul x (mathd327-one)) x))
    (implies
     (and
      (mathd327-real-p x)
      (not (equal x (mathd327-zero))))
     (equal
      (mathd327-mul x (mathd327-inv x))
      (mathd327-one)))
    (equal (mathd327-inv (mathd327-zero))
           (mathd327-zero))

    ;; Distributivity.
    (implies
     (and
      (mathd327-real-p x)
      (mathd327-real-p y)
      (mathd327-real-p z))
     (equal
      (mathd327-mul x (mathd327-add y z))
      (mathd327-add
       (mathd327-mul x y)
       (mathd327-mul x z)))))))

(defun-sk mathd327-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (mathd327-real-p x)
     (not (mathd327-lt x x)))
    (implies
     (and (mathd327-real-p x)
          (mathd327-real-p y))
     (or (mathd327-lt x y)
         (equal x y)
         (mathd327-lt y x)))
    (implies
     (and
      (mathd327-real-p x)
      (mathd327-real-p y)
      (mathd327-real-p z)
      (mathd327-lt x y)
      (mathd327-lt y z))
     (mathd327-lt x z))

    ;; Compatibility with addition and positive multiplication.
    (implies
     (and
      (mathd327-real-p x)
      (mathd327-real-p y)
      (mathd327-real-p z))
     (iff
      (mathd327-lt x y)
      (mathd327-lt
       (mathd327-add x z)
       (mathd327-add y z))))
    (implies
     (and
      (mathd327-real-p x)
      (mathd327-real-p y)
      (mathd327-lt (mathd327-zero) x)
      (mathd327-lt (mathd327-zero) y))
     (mathd327-lt
      (mathd327-zero)
      (mathd327-mul x y))))))

(defun-sk mathd327-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd327-real-p (mathd327-of-rational p))
     (equal (mathd327-of-rational 0)
            (mathd327-zero))
     (equal (mathd327-of-rational 1)
            (mathd327-one))
     (equal
      (mathd327-of-rational (+ p q))
      (mathd327-add
       (mathd327-of-rational p)
       (mathd327-of-rational q)))
     (equal
      (mathd327-of-rational (* p q))
      (mathd327-mul
       (mathd327-of-rational p)
       (mathd327-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd327-of-rational p)
       (mathd327-of-rational q)))
     (iff
      (< p q)
      (mathd327-lt
       (mathd327-of-rational p)
       (mathd327-of-rational q)))))))

(defun-sk mathd327-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd327-lt x (mathd327-natural n)))))

(defun-sk mathd327-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd327-real-p x)
    (mathd327-natural-bound-exists-p x))))

(defun mathd327-real-field-p ()
  (and
   (mathd327-real-p (mathd327-zero))
   (mathd327-real-p (mathd327-one))
   (not (equal (mathd327-zero) (mathd327-one)))
   (mathd327-lt (mathd327-zero) (mathd327-one))
   (mathd327-field-laws-p)
   (mathd327-order-laws-p)
   (mathd327-rational-laws-p)
   (mathd327-archimedean-p)))

(defun-sk mathd-algebra-327-statement-p ()
  (forall
   (a)
   (implies
    (and
     (mathd327-real-field-p)
     (mathd327-real-p a)
     (mathd327-lt
      (mathd327-mul
       (mathd327-of-rational 1/5)
       (mathd327-abs
        (mathd327-add
         (mathd327-of-rational 9)
         (mathd327-mul
          (mathd327-of-rational 2)
          a))))
      (mathd327-of-rational 1)))
    (and
     (mathd327-lt
      (mathd327-of-rational -7)
      a)
     (mathd327-lt
      a
      (mathd327-of-rational -2))))))

(value-triple :itpeval-statement-checked)
:q
