;; Statement-only formalization of miniF2F artifact algebra_amgm_sumasqdivbgeqsuma:
;; for positive reals a, b, c, and d,
;;   a^2/b + b^2/c + c^2/d + d^2/a >= a+b+c+d.
;; This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, and order below present an Archimedean
;; ordered field. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise encodes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub algamgm-real-p (value) t)
(defstub algamgm-zero () t)
(defstub algamgm-one () t)
(defstub algamgm-add (left right) t)
(defstub algamgm-mul (left right) t)
(defstub algamgm-neg (value) t)
(defstub algamgm-inv (value) t)
(defstub algamgm-lt (left right) t)
(defstub algamgm-of-rational (value) t)

(defun algamgm-div (left right)
  (algamgm-mul left (algamgm-inv right)))

(defun algamgm-le (left right)
  (or (algamgm-lt left right)
      (equal left right)))

(defun algamgm-abs (value)
  (if (algamgm-lt value (algamgm-zero))
      (algamgm-neg value)
    value))

(defun algamgm-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (algamgm-zero)
    (algamgm-add
     (algamgm-one)
     (algamgm-natural (1- n)))))

(defun-sk algamgm-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (algamgm-real-p x)
          (algamgm-real-p y))
     (and
      (algamgm-real-p (algamgm-add x y))
      (algamgm-real-p (algamgm-mul x y))))
    (implies
     (algamgm-real-p x)
     (and
      (algamgm-real-p (algamgm-neg x))
      (algamgm-real-p (algamgm-inv x))))

    ;; Additive commutative group.
    (implies
     (and
      (algamgm-real-p x)
      (algamgm-real-p y)
      (algamgm-real-p z))
     (equal
      (algamgm-add (algamgm-add x y) z)
      (algamgm-add x (algamgm-add y z))))
    (implies
     (and (algamgm-real-p x)
          (algamgm-real-p y))
     (equal (algamgm-add x y)
            (algamgm-add y x)))
    (implies
     (algamgm-real-p x)
     (and
      (equal (algamgm-add x (algamgm-zero)) x)
      (equal
       (algamgm-add x (algamgm-neg x))
       (algamgm-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and
      (algamgm-real-p x)
      (algamgm-real-p y)
      (algamgm-real-p z))
     (equal
      (algamgm-mul (algamgm-mul x y) z)
      (algamgm-mul x (algamgm-mul y z))))
    (implies
     (and (algamgm-real-p x)
          (algamgm-real-p y))
     (equal (algamgm-mul x y)
            (algamgm-mul y x)))
    (implies
     (algamgm-real-p x)
     (equal (algamgm-mul x (algamgm-one)) x))
    (implies
     (and
      (algamgm-real-p x)
      (not (equal x (algamgm-zero))))
     (equal
      (algamgm-mul x (algamgm-inv x))
      (algamgm-one)))
    (equal (algamgm-inv (algamgm-zero))
           (algamgm-zero))

    ;; Distributivity.
    (implies
     (and
      (algamgm-real-p x)
      (algamgm-real-p y)
      (algamgm-real-p z))
     (equal
      (algamgm-mul x (algamgm-add y z))
      (algamgm-add
       (algamgm-mul x y)
       (algamgm-mul x z)))))))

(defun-sk algamgm-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (algamgm-real-p x)
     (not (algamgm-lt x x)))
    (implies
     (and (algamgm-real-p x)
          (algamgm-real-p y))
     (or (algamgm-lt x y)
         (equal x y)
         (algamgm-lt y x)))
    (implies
     (and
      (algamgm-real-p x)
      (algamgm-real-p y)
      (algamgm-real-p z)
      (algamgm-lt x y)
      (algamgm-lt y z))
     (algamgm-lt x z))

    ;; Compatibility with addition and positive multiplication.
    (implies
     (and
      (algamgm-real-p x)
      (algamgm-real-p y)
      (algamgm-real-p z))
     (iff
      (algamgm-lt x y)
      (algamgm-lt
       (algamgm-add x z)
       (algamgm-add y z))))
    (implies
     (and
      (algamgm-real-p x)
      (algamgm-real-p y)
      (algamgm-lt (algamgm-zero) x)
      (algamgm-lt (algamgm-zero) y))
     (algamgm-lt
      (algamgm-zero)
      (algamgm-mul x y))))))

(defun-sk algamgm-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (algamgm-real-p (algamgm-of-rational p))
     (equal (algamgm-of-rational 0)
            (algamgm-zero))
     (equal (algamgm-of-rational 1)
            (algamgm-one))
     (equal
      (algamgm-of-rational (+ p q))
      (algamgm-add
       (algamgm-of-rational p)
       (algamgm-of-rational q)))
     (equal
      (algamgm-of-rational (* p q))
      (algamgm-mul
       (algamgm-of-rational p)
       (algamgm-of-rational q)))
     (iff
      (equal p q)
      (equal
       (algamgm-of-rational p)
       (algamgm-of-rational q)))
     (iff
      (< p q)
      (algamgm-lt
       (algamgm-of-rational p)
       (algamgm-of-rational q)))))))

(defun-sk algamgm-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (algamgm-lt x (algamgm-natural n)))))

(defun-sk algamgm-archimedean-p ()
  (forall
   (x)
   (implies
    (algamgm-real-p x)
    (algamgm-natural-bound-exists-p x))))

(defun algamgm-real-field-p ()
  (and
   (algamgm-real-p (algamgm-zero))
   (algamgm-real-p (algamgm-one))
   (not (equal (algamgm-zero) (algamgm-one)))
   (algamgm-lt (algamgm-zero) (algamgm-one))
   (algamgm-field-laws-p)
   (algamgm-order-laws-p)
   (algamgm-rational-laws-p)
   (algamgm-archimedean-p)))

(defun-sk algebra-amgm-sumasqdivbgeqsuma-statement-p ()
  (forall
   (a b c d)
   (implies
    (and
     (algamgm-real-field-p)
     (algamgm-real-p a)
     (algamgm-real-p b)
     (algamgm-real-p c)
     (algamgm-real-p d)
     (algamgm-lt (algamgm-zero) a)
     (algamgm-lt (algamgm-zero) b)
     (algamgm-lt (algamgm-zero) c)
     (algamgm-lt (algamgm-zero) d))
    (algamgm-le
     (algamgm-add
      (algamgm-add
       (algamgm-add a b)
       c)
      d)
     (algamgm-add
      (algamgm-add
       (algamgm-add
        (algamgm-div
         (algamgm-mul a a)
         b)
        (algamgm-div
         (algamgm-mul b b)
         c))
       (algamgm-div
        (algamgm-mul c c)
        d))
      (algamgm-div
       (algamgm-mul d d)
       a))))))

(value-triple :itpeval-statement-checked)
:q
