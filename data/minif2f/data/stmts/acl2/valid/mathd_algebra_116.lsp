;; Statement-only formalization of miniF2F artifact mathd_algebra_116:
        ;; if x=(13-sqrt(131))/4 and 2x^2-13x+k=0 over the reals, then k=19/4.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m116-real-p (value) t)
(defstub m116-zero () t)
(defstub m116-one () t)
(defstub m116-add (left right) t)
(defstub m116-mul (left right) t)
(defstub m116-neg (value) t)
(defstub m116-inv (value) t)
(defstub m116-lt (left right) t)
(defstub m116-of-rational (value) t)

(defun m116-sub (left right)
  (m116-add left (m116-neg right)))

(defun m116-div (left right)
  (m116-mul left (m116-inv right)))

(defun m116-le (left right)
  (or (equal left right) (m116-lt left right)))

(defun m116-nonnegative-p (value)
  (and (m116-real-p value)
       (m116-le (m116-zero) value)))

(defun m116-positive-p (value)
  (and (m116-real-p value)
       (m116-lt (m116-zero) value)))

(defun m116-abs (value)
  (if (m116-lt value (m116-zero))
      (m116-neg value)
    value))

(defun m116-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m116-one)
    (m116-mul
     value
     (m116-pow value (1- exponent)))))

(defun-sk m116-field-laws-p ()
  (forall (x y z)
    (and
     (m116-real-p (m116-zero))
     (m116-real-p (m116-one))
     (not (equal (m116-zero) (m116-one)))
     (implies
      (m116-real-p x)
      (and
       (m116-real-p (m116-neg x))
       (m116-real-p (m116-inv x))
       (equal (m116-add x (m116-zero)) x)
       (equal (m116-add x (m116-neg x))
              (m116-zero))
       (equal (m116-mul x (m116-one)) x)
       (implies
        (not (equal x (m116-zero)))
        (equal (m116-mul x (m116-inv x))
               (m116-one)))))
     (equal (m116-inv (m116-zero))
            (m116-zero))
     (implies
      (and (m116-real-p x)
           (m116-real-p y))
      (and
       (m116-real-p (m116-add x y))
       (m116-real-p (m116-mul x y))
       (equal (m116-add x y)
              (m116-add y x))
       (equal (m116-mul x y)
              (m116-mul y x))))
     (implies
      (and (m116-real-p x)
           (m116-real-p y)
           (m116-real-p z))
      (and
       (equal (m116-add (m116-add x y) z)
              (m116-add x (m116-add y z)))
       (equal (m116-mul (m116-mul x y) z)
              (m116-mul x (m116-mul y z)))
       (equal (m116-mul x (m116-add y z))
              (m116-add
               (m116-mul x y)
               (m116-mul x z))))))))

(defun-sk m116-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m116-real-p x)
          (m116-real-p y)
          (m116-real-p z))
     (and
      (not (m116-lt x x))
      (or (equal x y)
          (m116-lt x y)
          (m116-lt y x))
      (implies
       (and (m116-lt x y)
            (m116-lt y z))
       (m116-lt x z))
      (implies
       (m116-lt x y)
       (m116-lt
        (m116-add x z)
        (m116-add y z)))
      (implies
       (and (m116-lt (m116-zero) x)
            (m116-lt (m116-zero) y))
       (m116-lt
        (m116-zero)
        (m116-mul x y)))))))

(defun-sk m116-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m116-real-p (m116-of-rational a))
      (equal (m116-of-rational 0) (m116-zero))
      (equal (m116-of-rational 1) (m116-one))
      (equal
       (m116-of-rational (+ a b))
       (m116-add
        (m116-of-rational a)
        (m116-of-rational b)))
      (equal
       (m116-of-rational (* a b))
       (m116-mul
        (m116-of-rational a)
        (m116-of-rational b)))
      (equal
       (m116-of-rational (- a))
       (m116-neg (m116-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m116-of-rational a)
        (m116-of-rational b)))
      (iff
       (< a b)
       (m116-lt
        (m116-of-rational a)
        (m116-of-rational b)))))))

(defun m116-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m116-real-p (car coefficients))
     (m116-polynomial-p (cdr coefficients)))))

(defun m116-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m116-zero)
    (m116-add
     (car coefficients)
     (m116-mul
      x
      (m116-polynomial-value
       (cdr coefficients) x)))))

(defun m116-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m116-leading-coefficient (cdr coefficients))))

(defun m116-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m116-leading-coefficient coefficients)
     (m116-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m116-square-root-exists-p (x)
  (exists (root)
    (and
     (m116-nonnegative-p root)
     (equal (m116-mul root root) x))))

(defun-sk m116-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m116-nonnegative-p x)
     (m116-square-root-exists-p x))))

(defun-sk m116-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m116-real-p root)
     (equal
      (m116-polynomial-value coefficients root)
      (m116-zero)))))

(defun-sk m116-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m116-polynomial-p coefficients)
      (m116-odd-degree-p coefficients))
     (m116-polynomial-root-exists-p coefficients))))

(defun m116-real-closed-field-p ()
  (and
   (m116-field-laws-p)
   (m116-order-laws-p)
   (m116-rational-laws-p)
   (m116-lt (m116-zero) (m116-one))
   (m116-nonnegative-square-roots-p)
   (m116-odd-polynomial-roots-p)))

(defun m116-principal-square-root-p (root value)
  (and
   (m116-nonnegative-p root)
   (equal (m116-mul root root) value)))

(defchoose m116-sqrt (root) (value)
  (m116-principal-square-root-p root value))

        (defun mathd-algebra-116-statement (k x)
  (implies
   (and
    (m116-real-closed-field-p)
    (m116-real-p k)
    (m116-real-p x)
    (equal
     x
     (m116-div
      (m116-sub
       (m116-of-rational 13)
       (m116-sqrt (m116-of-rational 131)))
      (m116-of-rational 4)))
    (equal
     (m116-add
      (m116-sub
       (m116-mul
        (m116-of-rational 2)
        (m116-pow x 2))
       (m116-mul
        (m116-of-rational 13) x))
      k)
     (m116-zero)))
   (equal k (m116-of-rational 19/4))))

        (value-triple :itpeval-statement-checked)
        :q
