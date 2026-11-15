;; Statement-only formalization of miniF2F artifact mathd_algebra_510:
        ;; real x and y with x+y=13 and xy=24 have sqrt(x^2+y^2)=11.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m510-real-p (value) t)
(defstub m510-zero () t)
(defstub m510-one () t)
(defstub m510-add (left right) t)
(defstub m510-mul (left right) t)
(defstub m510-neg (value) t)
(defstub m510-inv (value) t)
(defstub m510-lt (left right) t)
(defstub m510-of-rational (value) t)

(defun m510-sub (left right)
  (m510-add left (m510-neg right)))

(defun m510-div (left right)
  (m510-mul left (m510-inv right)))

(defun m510-le (left right)
  (or (equal left right) (m510-lt left right)))

(defun m510-nonnegative-p (value)
  (and (m510-real-p value)
       (m510-le (m510-zero) value)))

(defun m510-positive-p (value)
  (and (m510-real-p value)
       (m510-lt (m510-zero) value)))

(defun m510-abs (value)
  (if (m510-lt value (m510-zero))
      (m510-neg value)
    value))

(defun m510-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m510-one)
    (m510-mul
     value
     (m510-pow value (1- exponent)))))

(defun-sk m510-field-laws-p ()
  (forall (x y z)
    (and
     (m510-real-p (m510-zero))
     (m510-real-p (m510-one))
     (not (equal (m510-zero) (m510-one)))
     (implies
      (m510-real-p x)
      (and
       (m510-real-p (m510-neg x))
       (m510-real-p (m510-inv x))
       (equal (m510-add x (m510-zero)) x)
       (equal (m510-add x (m510-neg x))
              (m510-zero))
       (equal (m510-mul x (m510-one)) x)
       (implies
        (not (equal x (m510-zero)))
        (equal (m510-mul x (m510-inv x))
               (m510-one)))))
     (equal (m510-inv (m510-zero))
            (m510-zero))
     (implies
      (and (m510-real-p x)
           (m510-real-p y))
      (and
       (m510-real-p (m510-add x y))
       (m510-real-p (m510-mul x y))
       (equal (m510-add x y)
              (m510-add y x))
       (equal (m510-mul x y)
              (m510-mul y x))))
     (implies
      (and (m510-real-p x)
           (m510-real-p y)
           (m510-real-p z))
      (and
       (equal (m510-add (m510-add x y) z)
              (m510-add x (m510-add y z)))
       (equal (m510-mul (m510-mul x y) z)
              (m510-mul x (m510-mul y z)))
       (equal (m510-mul x (m510-add y z))
              (m510-add
               (m510-mul x y)
               (m510-mul x z))))))))

(defun-sk m510-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m510-real-p x)
          (m510-real-p y)
          (m510-real-p z))
     (and
      (not (m510-lt x x))
      (or (equal x y)
          (m510-lt x y)
          (m510-lt y x))
      (implies
       (and (m510-lt x y)
            (m510-lt y z))
       (m510-lt x z))
      (implies
       (m510-lt x y)
       (m510-lt
        (m510-add x z)
        (m510-add y z)))
      (implies
       (and (m510-lt (m510-zero) x)
            (m510-lt (m510-zero) y))
       (m510-lt
        (m510-zero)
        (m510-mul x y)))))))

(defun-sk m510-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m510-real-p (m510-of-rational a))
      (equal (m510-of-rational 0) (m510-zero))
      (equal (m510-of-rational 1) (m510-one))
      (equal
       (m510-of-rational (+ a b))
       (m510-add
        (m510-of-rational a)
        (m510-of-rational b)))
      (equal
       (m510-of-rational (* a b))
       (m510-mul
        (m510-of-rational a)
        (m510-of-rational b)))
      (equal
       (m510-of-rational (- a))
       (m510-neg (m510-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m510-of-rational a)
        (m510-of-rational b)))
      (iff
       (< a b)
       (m510-lt
        (m510-of-rational a)
        (m510-of-rational b)))))))

(defun m510-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m510-real-p (car coefficients))
     (m510-polynomial-p (cdr coefficients)))))

(defun m510-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m510-zero)
    (m510-add
     (car coefficients)
     (m510-mul
      x
      (m510-polynomial-value
       (cdr coefficients) x)))))

(defun m510-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m510-leading-coefficient (cdr coefficients))))

(defun m510-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m510-leading-coefficient coefficients)
     (m510-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m510-square-root-exists-p (x)
  (exists (root)
    (and
     (m510-nonnegative-p root)
     (equal (m510-mul root root) x))))

(defun-sk m510-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m510-nonnegative-p x)
     (m510-square-root-exists-p x))))

(defun-sk m510-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m510-real-p root)
     (equal
      (m510-polynomial-value coefficients root)
      (m510-zero)))))

(defun-sk m510-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m510-polynomial-p coefficients)
      (m510-odd-degree-p coefficients))
     (m510-polynomial-root-exists-p coefficients))))

(defun m510-real-closed-field-p ()
  (and
   (m510-field-laws-p)
   (m510-order-laws-p)
   (m510-rational-laws-p)
   (m510-lt (m510-zero) (m510-one))
   (m510-nonnegative-square-roots-p)
   (m510-odd-polynomial-roots-p)))

(defun m510-principal-square-root-p (root value)
  (and
   (m510-nonnegative-p root)
   (equal (m510-mul root root) value)))

(defchoose m510-sqrt (root) (value)
  (m510-principal-square-root-p root value))

        (defun mathd-algebra-510-statement (x y)
  (implies
   (and
    (m510-real-closed-field-p)
    (m510-real-p x)
    (m510-real-p y)
    (equal
     (m510-add x y)
     (m510-of-rational 13))
    (equal
     (m510-mul x y)
     (m510-of-rational 24)))
   (equal
    (m510-sqrt
     (m510-add (m510-pow x 2) (m510-pow y 2)))
    (m510-of-rational 11))))

        (value-triple :itpeval-statement-checked)
        :q
