;; Statement-only formalization of miniF2F artifact algebra_apbon2pownleqapownpbpowon2:
        ;; for positive real a and b and positive natural n, the nth power of their arithmetic mean is at most the mean of their nth powers.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub jensen2-real-p (value) t)
(defstub jensen2-zero () t)
(defstub jensen2-one () t)
(defstub jensen2-add (left right) t)
(defstub jensen2-mul (left right) t)
(defstub jensen2-neg (value) t)
(defstub jensen2-inv (value) t)
(defstub jensen2-lt (left right) t)
(defstub jensen2-of-rational (value) t)

(defun jensen2-sub (left right)
  (jensen2-add left (jensen2-neg right)))

(defun jensen2-div (left right)
  (jensen2-mul left (jensen2-inv right)))

(defun jensen2-le (left right)
  (or (equal left right) (jensen2-lt left right)))

(defun jensen2-nonnegative-p (value)
  (and (jensen2-real-p value)
       (jensen2-le (jensen2-zero) value)))

(defun jensen2-positive-p (value)
  (and (jensen2-real-p value)
       (jensen2-lt (jensen2-zero) value)))

(defun jensen2-abs (value)
  (if (jensen2-lt value (jensen2-zero))
      (jensen2-neg value)
    value))

(defun jensen2-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (jensen2-one)
    (jensen2-mul
     value
     (jensen2-pow value (1- exponent)))))

(defun-sk jensen2-field-laws-p ()
  (forall (x y z)
    (and
     (jensen2-real-p (jensen2-zero))
     (jensen2-real-p (jensen2-one))
     (not (equal (jensen2-zero) (jensen2-one)))
     (implies
      (jensen2-real-p x)
      (and
       (jensen2-real-p (jensen2-neg x))
       (jensen2-real-p (jensen2-inv x))
       (equal (jensen2-add x (jensen2-zero)) x)
       (equal (jensen2-add x (jensen2-neg x))
              (jensen2-zero))
       (equal (jensen2-mul x (jensen2-one)) x)
       (implies
        (not (equal x (jensen2-zero)))
        (equal (jensen2-mul x (jensen2-inv x))
               (jensen2-one)))))
     (equal (jensen2-inv (jensen2-zero))
            (jensen2-zero))
     (implies
      (and (jensen2-real-p x)
           (jensen2-real-p y))
      (and
       (jensen2-real-p (jensen2-add x y))
       (jensen2-real-p (jensen2-mul x y))
       (equal (jensen2-add x y)
              (jensen2-add y x))
       (equal (jensen2-mul x y)
              (jensen2-mul y x))))
     (implies
      (and (jensen2-real-p x)
           (jensen2-real-p y)
           (jensen2-real-p z))
      (and
       (equal (jensen2-add (jensen2-add x y) z)
              (jensen2-add x (jensen2-add y z)))
       (equal (jensen2-mul (jensen2-mul x y) z)
              (jensen2-mul x (jensen2-mul y z)))
       (equal (jensen2-mul x (jensen2-add y z))
              (jensen2-add
               (jensen2-mul x y)
               (jensen2-mul x z))))))))

(defun-sk jensen2-order-laws-p ()
  (forall (x y z)
    (implies
     (and (jensen2-real-p x)
          (jensen2-real-p y)
          (jensen2-real-p z))
     (and
      (not (jensen2-lt x x))
      (or (equal x y)
          (jensen2-lt x y)
          (jensen2-lt y x))
      (implies
       (and (jensen2-lt x y)
            (jensen2-lt y z))
       (jensen2-lt x z))
      (implies
       (jensen2-lt x y)
       (jensen2-lt
        (jensen2-add x z)
        (jensen2-add y z)))
      (implies
       (and (jensen2-lt (jensen2-zero) x)
            (jensen2-lt (jensen2-zero) y))
       (jensen2-lt
        (jensen2-zero)
        (jensen2-mul x y)))))))

(defun-sk jensen2-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (jensen2-real-p (jensen2-of-rational a))
      (equal (jensen2-of-rational 0) (jensen2-zero))
      (equal (jensen2-of-rational 1) (jensen2-one))
      (equal
       (jensen2-of-rational (+ a b))
       (jensen2-add
        (jensen2-of-rational a)
        (jensen2-of-rational b)))
      (equal
       (jensen2-of-rational (* a b))
       (jensen2-mul
        (jensen2-of-rational a)
        (jensen2-of-rational b)))
      (equal
       (jensen2-of-rational (- a))
       (jensen2-neg (jensen2-of-rational a)))
      (iff
       (equal a b)
       (equal
        (jensen2-of-rational a)
        (jensen2-of-rational b)))
      (iff
       (< a b)
       (jensen2-lt
        (jensen2-of-rational a)
        (jensen2-of-rational b)))))))

(defun jensen2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (jensen2-real-p (car coefficients))
     (jensen2-polynomial-p (cdr coefficients)))))

(defun jensen2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (jensen2-zero)
    (jensen2-add
     (car coefficients)
     (jensen2-mul
      x
      (jensen2-polynomial-value
       (cdr coefficients) x)))))

(defun jensen2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (jensen2-leading-coefficient (cdr coefficients))))

(defun jensen2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (jensen2-leading-coefficient coefficients)
     (jensen2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk jensen2-square-root-exists-p (x)
  (exists (root)
    (and
     (jensen2-nonnegative-p root)
     (equal (jensen2-mul root root) x))))

(defun-sk jensen2-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (jensen2-nonnegative-p x)
     (jensen2-square-root-exists-p x))))

(defun-sk jensen2-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (jensen2-real-p root)
     (equal
      (jensen2-polynomial-value coefficients root)
      (jensen2-zero)))))

(defun-sk jensen2-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (jensen2-polynomial-p coefficients)
      (jensen2-odd-degree-p coefficients))
     (jensen2-polynomial-root-exists-p coefficients))))

(defun jensen2-real-closed-field-p ()
  (and
   (jensen2-field-laws-p)
   (jensen2-order-laws-p)
   (jensen2-rational-laws-p)
   (jensen2-lt (jensen2-zero) (jensen2-one))
   (jensen2-nonnegative-square-roots-p)
   (jensen2-odd-polynomial-roots-p)))

(defun jensen2-principal-square-root-p (root value)
  (and
   (jensen2-nonnegative-p root)
   (equal (jensen2-mul root root) value)))

(defchoose jensen2-sqrt (root) (value)
  (jensen2-principal-square-root-p root value))

        (defun algebra-apbon2pownleqapownpbpowon2-statement (a b n)
  (implies
   (and
    (jensen2-real-closed-field-p)
    (jensen2-positive-p a)
    (jensen2-positive-p b)
    (natp n)
    (< 0 n))
   (jensen2-le
    (jensen2-pow
     (jensen2-div
      (jensen2-add a b)
      (jensen2-of-rational 2))
     n)
    (jensen2-div
     (jensen2-add
      (jensen2-pow a n)
      (jensen2-pow b n))
     (jensen2-of-rational 2)))))

        (value-triple :itpeval-statement-checked)
        :q
