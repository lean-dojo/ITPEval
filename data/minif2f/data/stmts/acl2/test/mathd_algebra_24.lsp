;; Statement-only formalization of miniF2F artifact mathd_algebra_24:
;; every real x satisfying x / 50 = 40 is equal to 2000. This file
;; contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, and order below present an Archimedean
;; ordered field. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd24-real-p (value) t)
(defstub mathd24-zero () t)
(defstub mathd24-one () t)
(defstub mathd24-add (left right) t)
(defstub mathd24-mul (left right) t)
(defstub mathd24-neg (value) t)
(defstub mathd24-inv (value) t)
(defstub mathd24-lt (left right) t)
(defstub mathd24-of-rational (value) t)

(defun mathd24-div (left right)
  (mathd24-mul left (mathd24-inv right)))

(defun mathd24-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd24-zero)
    (mathd24-add
     (mathd24-one)
     (mathd24-natural (1- n)))))

(defun-sk mathd24-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (mathd24-real-p x)
          (mathd24-real-p y))
     (and
      (mathd24-real-p (mathd24-add x y))
      (mathd24-real-p (mathd24-mul x y))))
    (implies
     (mathd24-real-p x)
     (and
      (mathd24-real-p (mathd24-neg x))
      (mathd24-real-p (mathd24-inv x))))

    ;; Additive commutative group.
    (implies
     (and
      (mathd24-real-p x)
      (mathd24-real-p y)
      (mathd24-real-p z))
     (equal
      (mathd24-add (mathd24-add x y) z)
      (mathd24-add x (mathd24-add y z))))
    (implies
     (and (mathd24-real-p x)
          (mathd24-real-p y))
     (equal (mathd24-add x y)
            (mathd24-add y x)))
    (implies
     (mathd24-real-p x)
     (and
      (equal (mathd24-add x (mathd24-zero)) x)
      (equal
       (mathd24-add x (mathd24-neg x))
       (mathd24-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and
      (mathd24-real-p x)
      (mathd24-real-p y)
      (mathd24-real-p z))
     (equal
      (mathd24-mul (mathd24-mul x y) z)
      (mathd24-mul x (mathd24-mul y z))))
    (implies
     (and (mathd24-real-p x)
          (mathd24-real-p y))
     (equal (mathd24-mul x y)
            (mathd24-mul y x)))
    (implies
     (mathd24-real-p x)
     (equal (mathd24-mul x (mathd24-one)) x))
    (implies
     (and
      (mathd24-real-p x)
      (not (equal x (mathd24-zero))))
     (equal
      (mathd24-mul x (mathd24-inv x))
      (mathd24-one)))
    (equal (mathd24-inv (mathd24-zero))
           (mathd24-zero))

    ;; Distributivity.
    (implies
     (and
      (mathd24-real-p x)
      (mathd24-real-p y)
      (mathd24-real-p z))
     (equal
      (mathd24-mul x (mathd24-add y z))
      (mathd24-add
       (mathd24-mul x y)
       (mathd24-mul x z)))))))

(defun-sk mathd24-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (mathd24-real-p x)
     (not (mathd24-lt x x)))
    (implies
     (and (mathd24-real-p x)
          (mathd24-real-p y))
     (or (mathd24-lt x y)
         (equal x y)
         (mathd24-lt y x)))
    (implies
     (and
      (mathd24-real-p x)
      (mathd24-real-p y)
      (mathd24-real-p z)
      (mathd24-lt x y)
      (mathd24-lt y z))
     (mathd24-lt x z))

    ;; Compatibility with addition and positive multiplication.
    (implies
     (and
      (mathd24-real-p x)
      (mathd24-real-p y)
      (mathd24-real-p z))
     (iff
      (mathd24-lt x y)
      (mathd24-lt
       (mathd24-add x z)
       (mathd24-add y z))))
    (implies
     (and
      (mathd24-real-p x)
      (mathd24-real-p y)
      (mathd24-lt (mathd24-zero) x)
      (mathd24-lt (mathd24-zero) y))
     (mathd24-lt
      (mathd24-zero)
      (mathd24-mul x y))))))

(defun-sk mathd24-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd24-real-p (mathd24-of-rational p))
     (equal (mathd24-of-rational 0)
            (mathd24-zero))
     (equal (mathd24-of-rational 1)
            (mathd24-one))
     (equal
      (mathd24-of-rational (+ p q))
      (mathd24-add
       (mathd24-of-rational p)
       (mathd24-of-rational q)))
     (equal
      (mathd24-of-rational (* p q))
      (mathd24-mul
       (mathd24-of-rational p)
       (mathd24-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd24-of-rational p)
       (mathd24-of-rational q)))
     (iff
      (< p q)
      (mathd24-lt
       (mathd24-of-rational p)
       (mathd24-of-rational q)))))))

(defun-sk mathd24-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd24-lt x (mathd24-natural n)))))

(defun-sk mathd24-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd24-real-p x)
    (mathd24-natural-bound-exists-p x))))

(defun mathd24-real-field-p ()
  (and
   (mathd24-real-p (mathd24-zero))
   (mathd24-real-p (mathd24-one))
   (not (equal (mathd24-zero) (mathd24-one)))
   (mathd24-lt (mathd24-zero) (mathd24-one))
   (mathd24-field-laws-p)
   (mathd24-order-laws-p)
   (mathd24-rational-laws-p)
   (mathd24-archimedean-p)))

(defun-sk mathd-algebra-24-statement-p ()
  (forall
   (x)
   (implies
    (and
     (mathd24-real-field-p)
     (mathd24-real-p x)
     (equal
      (mathd24-div x (mathd24-of-rational 50))
      (mathd24-of-rational 40)))
    (equal x (mathd24-of-rational 2000)))))

(value-triple :itpeval-statement-checked)
:q
