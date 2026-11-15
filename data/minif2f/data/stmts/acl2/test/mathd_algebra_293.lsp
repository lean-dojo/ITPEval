;; Statement-only formalization of miniF2F artifact mathd_algebra_293:
        ;; for every nonnegative real x, the product of the three principal square roots equals 36*x*sqrt(35*x).
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m293-real-p (value) t)
(defstub m293-zero () t)
(defstub m293-one () t)
(defstub m293-add (left right) t)
(defstub m293-mul (left right) t)
(defstub m293-neg (value) t)
(defstub m293-inv (value) t)
(defstub m293-lt (left right) t)
(defstub m293-of-rational (value) t)

(defun m293-sub (left right)
  (m293-add left (m293-neg right)))

(defun m293-div (left right)
  (m293-mul left (m293-inv right)))

(defun m293-le (left right)
  (or (equal left right) (m293-lt left right)))

(defun m293-nonnegative-p (value)
  (and (m293-real-p value)
       (m293-le (m293-zero) value)))

(defun m293-positive-p (value)
  (and (m293-real-p value)
       (m293-lt (m293-zero) value)))

(defun m293-abs (value)
  (if (m293-lt value (m293-zero))
      (m293-neg value)
    value))

(defun m293-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m293-one)
    (m293-mul
     value
     (m293-pow value (1- exponent)))))

(defun-sk m293-field-laws-p ()
  (forall (x y z)
    (and
     (m293-real-p (m293-zero))
     (m293-real-p (m293-one))
     (not (equal (m293-zero) (m293-one)))
     (implies
      (m293-real-p x)
      (and
       (m293-real-p (m293-neg x))
       (m293-real-p (m293-inv x))
       (equal (m293-add x (m293-zero)) x)
       (equal (m293-add x (m293-neg x))
              (m293-zero))
       (equal (m293-mul x (m293-one)) x)
       (implies
        (not (equal x (m293-zero)))
        (equal (m293-mul x (m293-inv x))
               (m293-one)))))
     (equal (m293-inv (m293-zero))
            (m293-zero))
     (implies
      (and (m293-real-p x)
           (m293-real-p y))
      (and
       (m293-real-p (m293-add x y))
       (m293-real-p (m293-mul x y))
       (equal (m293-add x y)
              (m293-add y x))
       (equal (m293-mul x y)
              (m293-mul y x))))
     (implies
      (and (m293-real-p x)
           (m293-real-p y)
           (m293-real-p z))
      (and
       (equal (m293-add (m293-add x y) z)
              (m293-add x (m293-add y z)))
       (equal (m293-mul (m293-mul x y) z)
              (m293-mul x (m293-mul y z)))
       (equal (m293-mul x (m293-add y z))
              (m293-add
               (m293-mul x y)
               (m293-mul x z))))))))

(defun-sk m293-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m293-real-p x)
          (m293-real-p y)
          (m293-real-p z))
     (and
      (not (m293-lt x x))
      (or (equal x y)
          (m293-lt x y)
          (m293-lt y x))
      (implies
       (and (m293-lt x y)
            (m293-lt y z))
       (m293-lt x z))
      (implies
       (m293-lt x y)
       (m293-lt
        (m293-add x z)
        (m293-add y z)))
      (implies
       (and (m293-lt (m293-zero) x)
            (m293-lt (m293-zero) y))
       (m293-lt
        (m293-zero)
        (m293-mul x y)))))))

(defun-sk m293-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m293-real-p (m293-of-rational a))
      (equal (m293-of-rational 0) (m293-zero))
      (equal (m293-of-rational 1) (m293-one))
      (equal
       (m293-of-rational (+ a b))
       (m293-add
        (m293-of-rational a)
        (m293-of-rational b)))
      (equal
       (m293-of-rational (* a b))
       (m293-mul
        (m293-of-rational a)
        (m293-of-rational b)))
      (equal
       (m293-of-rational (- a))
       (m293-neg (m293-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m293-of-rational a)
        (m293-of-rational b)))
      (iff
       (< a b)
       (m293-lt
        (m293-of-rational a)
        (m293-of-rational b)))))))

(defun m293-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m293-real-p (car coefficients))
     (m293-polynomial-p (cdr coefficients)))))

(defun m293-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m293-zero)
    (m293-add
     (car coefficients)
     (m293-mul
      x
      (m293-polynomial-value
       (cdr coefficients) x)))))

(defun m293-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m293-leading-coefficient (cdr coefficients))))

(defun m293-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m293-leading-coefficient coefficients)
     (m293-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m293-square-root-exists-p (x)
  (exists (root)
    (and
     (m293-nonnegative-p root)
     (equal (m293-mul root root) x))))

(defun-sk m293-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m293-nonnegative-p x)
     (m293-square-root-exists-p x))))

(defun-sk m293-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m293-real-p root)
     (equal
      (m293-polynomial-value coefficients root)
      (m293-zero)))))

(defun-sk m293-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m293-polynomial-p coefficients)
      (m293-odd-degree-p coefficients))
     (m293-polynomial-root-exists-p coefficients))))

(defun m293-real-closed-field-p ()
  (and
   (m293-field-laws-p)
   (m293-order-laws-p)
   (m293-rational-laws-p)
   (m293-lt (m293-zero) (m293-one))
   (m293-nonnegative-square-roots-p)
   (m293-odd-polynomial-roots-p)))

(defun m293-principal-square-root-p (root value)
  (and
   (m293-nonnegative-p root)
   (equal (m293-mul root root) value)))

(defchoose m293-sqrt (root) (value)
  (m293-principal-square-root-p root value))

        (defun mathd-algebra-293-statement (x)
  (implies
   (and
    (m293-real-closed-field-p)
    (m293-nonnegative-p x))
   (equal
    (m293-mul
     (m293-mul
      (m293-sqrt
       (m293-mul (m293-of-rational 60) x))
      (m293-sqrt
       (m293-mul (m293-of-rational 12) x)))
     (m293-sqrt
      (m293-mul (m293-of-rational 63) x)))
    (m293-mul
     (m293-mul (m293-of-rational 36) x)
     (m293-sqrt
      (m293-mul (m293-of-rational 35) x))))))

        (value-triple :itpeval-statement-checked)
        :q
