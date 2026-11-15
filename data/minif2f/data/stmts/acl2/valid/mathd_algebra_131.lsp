;; Statement-only formalization of miniF2F artifact mathd_algebra_131:
        ;; distinct real roots a,b of 2x^2-7x+2 satisfy the stated reciprocal identity.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m131-real-p (value) t)
(defstub m131-zero () t)
(defstub m131-one () t)
(defstub m131-add (left right) t)
(defstub m131-mul (left right) t)
(defstub m131-neg (value) t)
(defstub m131-inv (value) t)
(defstub m131-lt (left right) t)
(defstub m131-of-rational (value) t)

(defun m131-sub (left right)
  (m131-add left (m131-neg right)))

(defun m131-div (left right)
  (m131-mul left (m131-inv right)))

(defun m131-le (left right)
  (or (equal left right) (m131-lt left right)))

(defun m131-nonnegative-p (value)
  (and (m131-real-p value)
       (m131-le (m131-zero) value)))

(defun m131-positive-p (value)
  (and (m131-real-p value)
       (m131-lt (m131-zero) value)))

(defun m131-abs (value)
  (if (m131-lt value (m131-zero))
      (m131-neg value)
    value))

(defun m131-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m131-one)
    (m131-mul
     value
     (m131-pow value (1- exponent)))))

(defun-sk m131-field-laws-p ()
  (forall (x y z)
    (and
     (m131-real-p (m131-zero))
     (m131-real-p (m131-one))
     (not (equal (m131-zero) (m131-one)))
     (implies
      (m131-real-p x)
      (and
       (m131-real-p (m131-neg x))
       (m131-real-p (m131-inv x))
       (equal (m131-add x (m131-zero)) x)
       (equal (m131-add x (m131-neg x))
              (m131-zero))
       (equal (m131-mul x (m131-one)) x)
       (implies
        (not (equal x (m131-zero)))
        (equal (m131-mul x (m131-inv x))
               (m131-one)))))
     (equal (m131-inv (m131-zero))
            (m131-zero))
     (implies
      (and (m131-real-p x)
           (m131-real-p y))
      (and
       (m131-real-p (m131-add x y))
       (m131-real-p (m131-mul x y))
       (equal (m131-add x y)
              (m131-add y x))
       (equal (m131-mul x y)
              (m131-mul y x))))
     (implies
      (and (m131-real-p x)
           (m131-real-p y)
           (m131-real-p z))
      (and
       (equal (m131-add (m131-add x y) z)
              (m131-add x (m131-add y z)))
       (equal (m131-mul (m131-mul x y) z)
              (m131-mul x (m131-mul y z)))
       (equal (m131-mul x (m131-add y z))
              (m131-add
               (m131-mul x y)
               (m131-mul x z))))))))

(defun-sk m131-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m131-real-p x)
          (m131-real-p y)
          (m131-real-p z))
     (and
      (not (m131-lt x x))
      (or (equal x y)
          (m131-lt x y)
          (m131-lt y x))
      (implies
       (and (m131-lt x y)
            (m131-lt y z))
       (m131-lt x z))
      (implies
       (m131-lt x y)
       (m131-lt
        (m131-add x z)
        (m131-add y z)))
      (implies
       (and (m131-lt (m131-zero) x)
            (m131-lt (m131-zero) y))
       (m131-lt
        (m131-zero)
        (m131-mul x y)))))))

(defun-sk m131-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m131-real-p (m131-of-rational a))
      (equal (m131-of-rational 0) (m131-zero))
      (equal (m131-of-rational 1) (m131-one))
      (equal
       (m131-of-rational (+ a b))
       (m131-add
        (m131-of-rational a)
        (m131-of-rational b)))
      (equal
       (m131-of-rational (* a b))
       (m131-mul
        (m131-of-rational a)
        (m131-of-rational b)))
      (equal
       (m131-of-rational (- a))
       (m131-neg (m131-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m131-of-rational a)
        (m131-of-rational b)))
      (iff
       (< a b)
       (m131-lt
        (m131-of-rational a)
        (m131-of-rational b)))))))

(defun m131-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m131-real-p (car coefficients))
     (m131-polynomial-p (cdr coefficients)))))

(defun m131-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m131-zero)
    (m131-add
     (car coefficients)
     (m131-mul
      x
      (m131-polynomial-value
       (cdr coefficients) x)))))

(defun m131-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m131-leading-coefficient (cdr coefficients))))

(defun m131-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m131-leading-coefficient coefficients)
     (m131-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m131-square-root-exists-p (x)
  (exists (root)
    (and
     (m131-nonnegative-p root)
     (equal (m131-mul root root) x))))

(defun-sk m131-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m131-nonnegative-p x)
     (m131-square-root-exists-p x))))

(defun-sk m131-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m131-real-p root)
     (equal
      (m131-polynomial-value coefficients root)
      (m131-zero)))))

(defun-sk m131-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m131-polynomial-p coefficients)
      (m131-odd-degree-p coefficients))
     (m131-polynomial-root-exists-p coefficients))))

(defun m131-real-closed-field-p ()
  (and
   (m131-field-laws-p)
   (m131-order-laws-p)
   (m131-rational-laws-p)
   (m131-lt (m131-zero) (m131-one))
   (m131-nonnegative-square-roots-p)
   (m131-odd-polynomial-roots-p)))

(defun m131-principal-square-root-p (root value)
  (and
   (m131-nonnegative-p root)
   (equal (m131-mul root root) value)))

(defchoose m131-sqrt (root) (value)
  (m131-principal-square-root-p root value))

        (defun m131-polynomial (x)
  (m131-add
   (m131-sub
    (m131-mul (m131-of-rational 2) (m131-pow x 2))
    (m131-mul (m131-of-rational 7) x))
   (m131-of-rational 2)))

(defun mathd-algebra-131-statement (a b)
  (implies
   (and
    (m131-real-closed-field-p)
    (m131-real-p a)
    (m131-real-p b)
    (equal (m131-polynomial a) (m131-zero))
    (equal (m131-polynomial b) (m131-zero))
    (not (equal a b)))
   (equal
    (m131-add
     (m131-div
      (m131-one)
      (m131-sub a (m131-one)))
     (m131-div
      (m131-one)
      (m131-sub b (m131-one))))
    (m131-of-rational -1))))

        (value-triple :itpeval-statement-checked)
        :q
