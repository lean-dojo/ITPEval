;; Statement-only formalization of miniF2F artifact mathd_algebra_44:
        ;; real numbers s and t satisfying s = 9 - 2t and t = 3s + 1 must satisfy s = 1 and t = 4.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m44-real-p (value) t)
(defstub m44-zero () t)
(defstub m44-one () t)
(defstub m44-add (left right) t)
(defstub m44-mul (left right) t)
(defstub m44-neg (value) t)
(defstub m44-inv (value) t)
(defstub m44-lt (left right) t)
(defstub m44-of-rational (value) t)

(defun m44-sub (left right)
  (m44-add left (m44-neg right)))

(defun m44-div (left right)
  (m44-mul left (m44-inv right)))

(defun m44-le (left right)
  (or (equal left right) (m44-lt left right)))

(defun m44-nonnegative-p (value)
  (and (m44-real-p value)
       (m44-le (m44-zero) value)))

(defun m44-positive-p (value)
  (and (m44-real-p value)
       (m44-lt (m44-zero) value)))

(defun m44-abs (value)
  (if (m44-lt value (m44-zero))
      (m44-neg value)
    value))

(defun m44-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m44-one)
    (m44-mul
     value
     (m44-pow value (1- exponent)))))

(defun-sk m44-field-laws-p ()
  (forall (x y z)
    (and
     (m44-real-p (m44-zero))
     (m44-real-p (m44-one))
     (not (equal (m44-zero) (m44-one)))
     (implies
      (m44-real-p x)
      (and
       (m44-real-p (m44-neg x))
       (m44-real-p (m44-inv x))
       (equal (m44-add x (m44-zero)) x)
       (equal (m44-add x (m44-neg x))
              (m44-zero))
       (equal (m44-mul x (m44-one)) x)
       (implies
        (not (equal x (m44-zero)))
        (equal (m44-mul x (m44-inv x))
               (m44-one)))))
     (equal (m44-inv (m44-zero))
            (m44-zero))
     (implies
      (and (m44-real-p x)
           (m44-real-p y))
      (and
       (m44-real-p (m44-add x y))
       (m44-real-p (m44-mul x y))
       (equal (m44-add x y)
              (m44-add y x))
       (equal (m44-mul x y)
              (m44-mul y x))))
     (implies
      (and (m44-real-p x)
           (m44-real-p y)
           (m44-real-p z))
      (and
       (equal (m44-add (m44-add x y) z)
              (m44-add x (m44-add y z)))
       (equal (m44-mul (m44-mul x y) z)
              (m44-mul x (m44-mul y z)))
       (equal (m44-mul x (m44-add y z))
              (m44-add
               (m44-mul x y)
               (m44-mul x z))))))))

(defun-sk m44-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m44-real-p x)
          (m44-real-p y)
          (m44-real-p z))
     (and
      (not (m44-lt x x))
      (or (equal x y)
          (m44-lt x y)
          (m44-lt y x))
      (implies
       (and (m44-lt x y)
            (m44-lt y z))
       (m44-lt x z))
      (implies
       (m44-lt x y)
       (m44-lt
        (m44-add x z)
        (m44-add y z)))
      (implies
       (and (m44-lt (m44-zero) x)
            (m44-lt (m44-zero) y))
       (m44-lt
        (m44-zero)
        (m44-mul x y)))))))

(defun-sk m44-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m44-real-p (m44-of-rational a))
      (equal (m44-of-rational 0) (m44-zero))
      (equal (m44-of-rational 1) (m44-one))
      (equal
       (m44-of-rational (+ a b))
       (m44-add
        (m44-of-rational a)
        (m44-of-rational b)))
      (equal
       (m44-of-rational (* a b))
       (m44-mul
        (m44-of-rational a)
        (m44-of-rational b)))
      (equal
       (m44-of-rational (- a))
       (m44-neg (m44-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m44-of-rational a)
        (m44-of-rational b)))
      (iff
       (< a b)
       (m44-lt
        (m44-of-rational a)
        (m44-of-rational b)))))))

(defun m44-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m44-real-p (car coefficients))
     (m44-polynomial-p (cdr coefficients)))))

(defun m44-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m44-zero)
    (m44-add
     (car coefficients)
     (m44-mul
      x
      (m44-polynomial-value
       (cdr coefficients) x)))))

(defun m44-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m44-leading-coefficient (cdr coefficients))))

(defun m44-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m44-leading-coefficient coefficients)
     (m44-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m44-square-root-exists-p (x)
  (exists (root)
    (and
     (m44-nonnegative-p root)
     (equal (m44-mul root root) x))))

(defun-sk m44-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m44-nonnegative-p x)
     (m44-square-root-exists-p x))))

(defun-sk m44-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m44-real-p root)
     (equal
      (m44-polynomial-value coefficients root)
      (m44-zero)))))

(defun-sk m44-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m44-polynomial-p coefficients)
      (m44-odd-degree-p coefficients))
     (m44-polynomial-root-exists-p coefficients))))

(defun m44-real-closed-field-p ()
  (and
   (m44-field-laws-p)
   (m44-order-laws-p)
   (m44-rational-laws-p)
   (m44-lt (m44-zero) (m44-one))
   (m44-nonnegative-square-roots-p)
   (m44-odd-polynomial-roots-p)))

(defun m44-principal-square-root-p (root value)
  (and
   (m44-nonnegative-p root)
   (equal (m44-mul root root) value)))

(defchoose m44-sqrt (root) (value)
  (m44-principal-square-root-p root value))

        (defun mathd-algebra-44-statement (s t-value)
  (implies
   (and
    (m44-real-closed-field-p)
    (m44-real-p s)
    (m44-real-p t-value)
    (equal
     s
     (m44-sub
      (m44-of-rational 9)
      (m44-mul (m44-of-rational 2) t-value)))
    (equal
     t-value
     (m44-add
      (m44-mul (m44-of-rational 3) s)
      (m44-of-rational 1))))
   (and
    (equal s (m44-of-rational 1))
    (equal t-value (m44-of-rational 4)))))

        (value-triple :itpeval-statement-checked)
        :q
