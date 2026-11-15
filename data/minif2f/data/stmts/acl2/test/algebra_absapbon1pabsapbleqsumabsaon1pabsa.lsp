;; Statement-only formalization of miniF2F artifact algebra_absapbon1pabsapbleqsumabsaon1pabsa:
;; for all reals a and b,
;;   |a+b|/(1+|a+b|) <= |a|/(1+|a|) + |b|/(1+|b|).
;; This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, and order below present an Archimedean
;; ordered field. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub algabs-real-p (value) t)
(defstub algabs-zero () t)
(defstub algabs-one () t)
(defstub algabs-add (left right) t)
(defstub algabs-mul (left right) t)
(defstub algabs-neg (value) t)
(defstub algabs-inv (value) t)
(defstub algabs-lt (left right) t)
(defstub algabs-of-rational (value) t)

(defun algabs-div (left right)
  (algabs-mul left (algabs-inv right)))

(defun algabs-le (left right)
  (or (algabs-lt left right)
      (equal left right)))

(defun algabs-abs (value)
  (if (algabs-lt value (algabs-zero))
      (algabs-neg value)
    value))

(defun algabs-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (algabs-zero)
    (algabs-add
     (algabs-one)
     (algabs-natural (1- n)))))

(defun-sk algabs-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (algabs-real-p x)
          (algabs-real-p y))
     (and
      (algabs-real-p (algabs-add x y))
      (algabs-real-p (algabs-mul x y))))
    (implies
     (algabs-real-p x)
     (and
      (algabs-real-p (algabs-neg x))
      (algabs-real-p (algabs-inv x))))

    ;; Additive commutative group.
    (implies
     (and
      (algabs-real-p x)
      (algabs-real-p y)
      (algabs-real-p z))
     (equal
      (algabs-add (algabs-add x y) z)
      (algabs-add x (algabs-add y z))))
    (implies
     (and (algabs-real-p x)
          (algabs-real-p y))
     (equal (algabs-add x y)
            (algabs-add y x)))
    (implies
     (algabs-real-p x)
     (and
      (equal (algabs-add x (algabs-zero)) x)
      (equal
       (algabs-add x (algabs-neg x))
       (algabs-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and
      (algabs-real-p x)
      (algabs-real-p y)
      (algabs-real-p z))
     (equal
      (algabs-mul (algabs-mul x y) z)
      (algabs-mul x (algabs-mul y z))))
    (implies
     (and (algabs-real-p x)
          (algabs-real-p y))
     (equal (algabs-mul x y)
            (algabs-mul y x)))
    (implies
     (algabs-real-p x)
     (equal (algabs-mul x (algabs-one)) x))
    (implies
     (and
      (algabs-real-p x)
      (not (equal x (algabs-zero))))
     (equal
      (algabs-mul x (algabs-inv x))
      (algabs-one)))
    (equal (algabs-inv (algabs-zero))
           (algabs-zero))

    ;; Distributivity.
    (implies
     (and
      (algabs-real-p x)
      (algabs-real-p y)
      (algabs-real-p z))
     (equal
      (algabs-mul x (algabs-add y z))
      (algabs-add
       (algabs-mul x y)
       (algabs-mul x z)))))))

(defun-sk algabs-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (algabs-real-p x)
     (not (algabs-lt x x)))
    (implies
     (and (algabs-real-p x)
          (algabs-real-p y))
     (or (algabs-lt x y)
         (equal x y)
         (algabs-lt y x)))
    (implies
     (and
      (algabs-real-p x)
      (algabs-real-p y)
      (algabs-real-p z)
      (algabs-lt x y)
      (algabs-lt y z))
     (algabs-lt x z))

    ;; Compatibility with addition and positive multiplication.
    (implies
     (and
      (algabs-real-p x)
      (algabs-real-p y)
      (algabs-real-p z))
     (iff
      (algabs-lt x y)
      (algabs-lt
       (algabs-add x z)
       (algabs-add y z))))
    (implies
     (and
      (algabs-real-p x)
      (algabs-real-p y)
      (algabs-lt (algabs-zero) x)
      (algabs-lt (algabs-zero) y))
     (algabs-lt
      (algabs-zero)
      (algabs-mul x y))))))

(defun-sk algabs-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (algabs-real-p (algabs-of-rational p))
     (equal (algabs-of-rational 0)
            (algabs-zero))
     (equal (algabs-of-rational 1)
            (algabs-one))
     (equal
      (algabs-of-rational (+ p q))
      (algabs-add
       (algabs-of-rational p)
       (algabs-of-rational q)))
     (equal
      (algabs-of-rational (* p q))
      (algabs-mul
       (algabs-of-rational p)
       (algabs-of-rational q)))
     (iff
      (equal p q)
      (equal
       (algabs-of-rational p)
       (algabs-of-rational q)))
     (iff
      (< p q)
      (algabs-lt
       (algabs-of-rational p)
       (algabs-of-rational q)))))))

(defun-sk algabs-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (algabs-lt x (algabs-natural n)))))

(defun-sk algabs-archimedean-p ()
  (forall
   (x)
   (implies
    (algabs-real-p x)
    (algabs-natural-bound-exists-p x))))

(defun algabs-real-field-p ()
  (and
   (algabs-real-p (algabs-zero))
   (algabs-real-p (algabs-one))
   (not (equal (algabs-zero) (algabs-one)))
   (algabs-lt (algabs-zero) (algabs-one))
   (algabs-field-laws-p)
   (algabs-order-laws-p)
   (algabs-rational-laws-p)
   (algabs-archimedean-p)))

(defun-sk algebra-absapbon1pabsapbleqsumabsaon1pabsa-statement-p ()
  (forall
   (a b)
   (implies
    (and
     (algabs-real-field-p)
     (algabs-real-p a)
     (algabs-real-p b))
    (algabs-le
     (algabs-div
      (algabs-abs (algabs-add a b))
      (algabs-add
       (algabs-of-rational 1)
       (algabs-abs (algabs-add a b))))
     (algabs-add
      (algabs-div
       (algabs-abs a)
       (algabs-add
        (algabs-of-rational 1)
        (algabs-abs a)))
      (algabs-div
       (algabs-abs b)
       (algabs-add
        (algabs-of-rational 1)
        (algabs-abs b))))))))

(value-triple :itpeval-statement-checked)
:q
