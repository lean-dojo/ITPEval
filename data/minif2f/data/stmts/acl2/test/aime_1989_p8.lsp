;; Statement-only formalization of miniF2F artifact aime_1989_p8:
        ;; three rational-linear equations in seven real variables imply the fourth weighted equation.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime89p8-real-p (value) t)
(defstub aime89p8-zero () t)
(defstub aime89p8-one () t)
(defstub aime89p8-add (left right) t)
(defstub aime89p8-mul (left right) t)
(defstub aime89p8-neg (value) t)
(defstub aime89p8-inv (value) t)
(defstub aime89p8-lt (left right) t)
(defstub aime89p8-of-rational (value) t)

(defun aime89p8-sub (left right)
  (aime89p8-add left (aime89p8-neg right)))

(defun aime89p8-div (left right)
  (aime89p8-mul left (aime89p8-inv right)))

(defun aime89p8-le (left right)
  (or (equal left right) (aime89p8-lt left right)))

(defun aime89p8-nonnegative-p (value)
  (and (aime89p8-real-p value)
       (aime89p8-le (aime89p8-zero) value)))

(defun aime89p8-positive-p (value)
  (and (aime89p8-real-p value)
       (aime89p8-lt (aime89p8-zero) value)))

(defun aime89p8-abs (value)
  (if (aime89p8-lt value (aime89p8-zero))
      (aime89p8-neg value)
    value))

(defun aime89p8-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime89p8-one)
    (aime89p8-mul
     value
     (aime89p8-pow value (1- exponent)))))

(defun-sk aime89p8-field-laws-p ()
  (forall (x y z)
    (and
     (aime89p8-real-p (aime89p8-zero))
     (aime89p8-real-p (aime89p8-one))
     (not (equal (aime89p8-zero) (aime89p8-one)))
     (implies
      (aime89p8-real-p x)
      (and
       (aime89p8-real-p (aime89p8-neg x))
       (aime89p8-real-p (aime89p8-inv x))
       (equal (aime89p8-add x (aime89p8-zero)) x)
       (equal (aime89p8-add x (aime89p8-neg x))
              (aime89p8-zero))
       (equal (aime89p8-mul x (aime89p8-one)) x)
       (implies
        (not (equal x (aime89p8-zero)))
        (equal (aime89p8-mul x (aime89p8-inv x))
               (aime89p8-one)))))
     (equal (aime89p8-inv (aime89p8-zero))
            (aime89p8-zero))
     (implies
      (and (aime89p8-real-p x)
           (aime89p8-real-p y))
      (and
       (aime89p8-real-p (aime89p8-add x y))
       (aime89p8-real-p (aime89p8-mul x y))
       (equal (aime89p8-add x y)
              (aime89p8-add y x))
       (equal (aime89p8-mul x y)
              (aime89p8-mul y x))))
     (implies
      (and (aime89p8-real-p x)
           (aime89p8-real-p y)
           (aime89p8-real-p z))
      (and
       (equal (aime89p8-add (aime89p8-add x y) z)
              (aime89p8-add x (aime89p8-add y z)))
       (equal (aime89p8-mul (aime89p8-mul x y) z)
              (aime89p8-mul x (aime89p8-mul y z)))
       (equal (aime89p8-mul x (aime89p8-add y z))
              (aime89p8-add
               (aime89p8-mul x y)
               (aime89p8-mul x z))))))))

(defun-sk aime89p8-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime89p8-real-p x)
          (aime89p8-real-p y)
          (aime89p8-real-p z))
     (and
      (not (aime89p8-lt x x))
      (or (equal x y)
          (aime89p8-lt x y)
          (aime89p8-lt y x))
      (implies
       (and (aime89p8-lt x y)
            (aime89p8-lt y z))
       (aime89p8-lt x z))
      (implies
       (aime89p8-lt x y)
       (aime89p8-lt
        (aime89p8-add x z)
        (aime89p8-add y z)))
      (implies
       (and (aime89p8-lt (aime89p8-zero) x)
            (aime89p8-lt (aime89p8-zero) y))
       (aime89p8-lt
        (aime89p8-zero)
        (aime89p8-mul x y)))))))

(defun-sk aime89p8-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime89p8-real-p (aime89p8-of-rational a))
      (equal (aime89p8-of-rational 0) (aime89p8-zero))
      (equal (aime89p8-of-rational 1) (aime89p8-one))
      (equal
       (aime89p8-of-rational (+ a b))
       (aime89p8-add
        (aime89p8-of-rational a)
        (aime89p8-of-rational b)))
      (equal
       (aime89p8-of-rational (* a b))
       (aime89p8-mul
        (aime89p8-of-rational a)
        (aime89p8-of-rational b)))
      (equal
       (aime89p8-of-rational (- a))
       (aime89p8-neg (aime89p8-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime89p8-of-rational a)
        (aime89p8-of-rational b)))
      (iff
       (< a b)
       (aime89p8-lt
        (aime89p8-of-rational a)
        (aime89p8-of-rational b)))))))

(defun aime89p8-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime89p8-real-p (car coefficients))
     (aime89p8-polynomial-p (cdr coefficients)))))

(defun aime89p8-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime89p8-zero)
    (aime89p8-add
     (car coefficients)
     (aime89p8-mul
      x
      (aime89p8-polynomial-value
       (cdr coefficients) x)))))

(defun aime89p8-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime89p8-leading-coefficient (cdr coefficients))))

(defun aime89p8-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime89p8-leading-coefficient coefficients)
     (aime89p8-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime89p8-square-root-exists-p (x)
  (exists (root)
    (and
     (aime89p8-nonnegative-p root)
     (equal (aime89p8-mul root root) x))))

(defun-sk aime89p8-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime89p8-nonnegative-p x)
     (aime89p8-square-root-exists-p x))))

(defun-sk aime89p8-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime89p8-real-p root)
     (equal
      (aime89p8-polynomial-value coefficients root)
      (aime89p8-zero)))))

(defun-sk aime89p8-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime89p8-polynomial-p coefficients)
      (aime89p8-odd-degree-p coefficients))
     (aime89p8-polynomial-root-exists-p coefficients))))

(defun aime89p8-real-closed-field-p ()
  (and
   (aime89p8-field-laws-p)
   (aime89p8-order-laws-p)
   (aime89p8-rational-laws-p)
   (aime89p8-lt (aime89p8-zero) (aime89p8-one))
   (aime89p8-nonnegative-square-roots-p)
   (aime89p8-odd-polynomial-roots-p)))

(defun aime89p8-principal-square-root-p (root value)
  (and
   (aime89p8-nonnegative-p root)
   (equal (aime89p8-mul root root) value)))

(defchoose aime89p8-sqrt (root) (value)
  (aime89p8-principal-square-root-p root value))

        (defun aime89p8-scale (coefficient value)
  (aime89p8-mul
   (aime89p8-of-rational coefficient)
   value))

(defun aime89p8-linear-combination
    (qa qb qc qd qe qf qg a b c d e f g)
  (aime89p8-add
   (aime89p8-scale qa a)
   (aime89p8-add
    (aime89p8-scale qb b)
    (aime89p8-add
     (aime89p8-scale qc c)
     (aime89p8-add
      (aime89p8-scale qd d)
      (aime89p8-add
       (aime89p8-scale qe e)
       (aime89p8-add
        (aime89p8-scale qf f)
        (aime89p8-scale qg g))))))))

(defun aime-1989-p8-statement (a b c d e f g)
  (implies
   (and
    (aime89p8-real-closed-field-p)
    (aime89p8-real-p a)
    (aime89p8-real-p b)
    (aime89p8-real-p c)
    (aime89p8-real-p d)
    (aime89p8-real-p e)
    (aime89p8-real-p f)
    (aime89p8-real-p g)
    (equal
     (aime89p8-linear-combination
      1 4 9 16 25 36 49 a b c d e f g)
     (aime89p8-of-rational 1))
    (equal
     (aime89p8-linear-combination
      4 9 16 25 36 49 64 a b c d e f g)
     (aime89p8-of-rational 12))
    (equal
     (aime89p8-linear-combination
      9 16 25 36 49 64 81 a b c d e f g)
     (aime89p8-of-rational 123)))
   (equal
    (aime89p8-linear-combination
     16 25 36 49 64 81 100 a b c d e f g)
    (aime89p8-of-rational 334))))

        (value-triple :itpeval-statement-checked)
        :q
