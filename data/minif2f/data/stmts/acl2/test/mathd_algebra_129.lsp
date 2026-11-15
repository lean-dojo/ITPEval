;; Statement-only formalization of miniF2F artifact mathd_algebra_129:
        ;; a nonzero real a satisfying 8^-1 / 4^-1 - a^-1 = 1 equals -2.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m129-real-p (value) t)
(defstub m129-zero () t)
(defstub m129-one () t)
(defstub m129-add (left right) t)
(defstub m129-mul (left right) t)
(defstub m129-neg (value) t)
(defstub m129-inv (value) t)
(defstub m129-lt (left right) t)
(defstub m129-of-rational (value) t)

(defun m129-sub (left right)
  (m129-add left (m129-neg right)))

(defun m129-div (left right)
  (m129-mul left (m129-inv right)))

(defun m129-le (left right)
  (or (equal left right) (m129-lt left right)))

(defun m129-nonnegative-p (value)
  (and (m129-real-p value)
       (m129-le (m129-zero) value)))

(defun m129-positive-p (value)
  (and (m129-real-p value)
       (m129-lt (m129-zero) value)))

(defun m129-abs (value)
  (if (m129-lt value (m129-zero))
      (m129-neg value)
    value))

(defun m129-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m129-one)
    (m129-mul
     value
     (m129-pow value (1- exponent)))))

(defun-sk m129-field-laws-p ()
  (forall (x y z)
    (and
     (m129-real-p (m129-zero))
     (m129-real-p (m129-one))
     (not (equal (m129-zero) (m129-one)))
     (implies
      (m129-real-p x)
      (and
       (m129-real-p (m129-neg x))
       (m129-real-p (m129-inv x))
       (equal (m129-add x (m129-zero)) x)
       (equal (m129-add x (m129-neg x))
              (m129-zero))
       (equal (m129-mul x (m129-one)) x)
       (implies
        (not (equal x (m129-zero)))
        (equal (m129-mul x (m129-inv x))
               (m129-one)))))
     (equal (m129-inv (m129-zero))
            (m129-zero))
     (implies
      (and (m129-real-p x)
           (m129-real-p y))
      (and
       (m129-real-p (m129-add x y))
       (m129-real-p (m129-mul x y))
       (equal (m129-add x y)
              (m129-add y x))
       (equal (m129-mul x y)
              (m129-mul y x))))
     (implies
      (and (m129-real-p x)
           (m129-real-p y)
           (m129-real-p z))
      (and
       (equal (m129-add (m129-add x y) z)
              (m129-add x (m129-add y z)))
       (equal (m129-mul (m129-mul x y) z)
              (m129-mul x (m129-mul y z)))
       (equal (m129-mul x (m129-add y z))
              (m129-add
               (m129-mul x y)
               (m129-mul x z))))))))

(defun-sk m129-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m129-real-p x)
          (m129-real-p y)
          (m129-real-p z))
     (and
      (not (m129-lt x x))
      (or (equal x y)
          (m129-lt x y)
          (m129-lt y x))
      (implies
       (and (m129-lt x y)
            (m129-lt y z))
       (m129-lt x z))
      (implies
       (m129-lt x y)
       (m129-lt
        (m129-add x z)
        (m129-add y z)))
      (implies
       (and (m129-lt (m129-zero) x)
            (m129-lt (m129-zero) y))
       (m129-lt
        (m129-zero)
        (m129-mul x y)))))))

(defun-sk m129-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m129-real-p (m129-of-rational a))
      (equal (m129-of-rational 0) (m129-zero))
      (equal (m129-of-rational 1) (m129-one))
      (equal
       (m129-of-rational (+ a b))
       (m129-add
        (m129-of-rational a)
        (m129-of-rational b)))
      (equal
       (m129-of-rational (* a b))
       (m129-mul
        (m129-of-rational a)
        (m129-of-rational b)))
      (equal
       (m129-of-rational (- a))
       (m129-neg (m129-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m129-of-rational a)
        (m129-of-rational b)))
      (iff
       (< a b)
       (m129-lt
        (m129-of-rational a)
        (m129-of-rational b)))))))

(defun m129-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m129-real-p (car coefficients))
     (m129-polynomial-p (cdr coefficients)))))

(defun m129-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m129-zero)
    (m129-add
     (car coefficients)
     (m129-mul
      x
      (m129-polynomial-value
       (cdr coefficients) x)))))

(defun m129-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m129-leading-coefficient (cdr coefficients))))

(defun m129-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m129-leading-coefficient coefficients)
     (m129-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m129-square-root-exists-p (x)
  (exists (root)
    (and
     (m129-nonnegative-p root)
     (equal (m129-mul root root) x))))

(defun-sk m129-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m129-nonnegative-p x)
     (m129-square-root-exists-p x))))

(defun-sk m129-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m129-real-p root)
     (equal
      (m129-polynomial-value coefficients root)
      (m129-zero)))))

(defun-sk m129-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m129-polynomial-p coefficients)
      (m129-odd-degree-p coefficients))
     (m129-polynomial-root-exists-p coefficients))))

(defun m129-real-closed-field-p ()
  (and
   (m129-field-laws-p)
   (m129-order-laws-p)
   (m129-rational-laws-p)
   (m129-lt (m129-zero) (m129-one))
   (m129-nonnegative-square-roots-p)
   (m129-odd-polynomial-roots-p)))

(defun m129-principal-square-root-p (root value)
  (and
   (m129-nonnegative-p root)
   (equal (m129-mul root root) value)))

(defchoose m129-sqrt (root) (value)
  (m129-principal-square-root-p root value))

        (defun mathd-algebra-129-statement (a)
  (implies
   (and
    (m129-real-closed-field-p)
    (m129-real-p a)
    (not (equal a (m129-zero)))
    (equal
     (m129-sub
      (m129-div
       (m129-inv (m129-of-rational 8))
       (m129-inv (m129-of-rational 4)))
      (m129-inv a))
     (m129-one)))
   (equal a (m129-of-rational -2))))

        (value-triple :itpeval-statement-checked)
        :q
