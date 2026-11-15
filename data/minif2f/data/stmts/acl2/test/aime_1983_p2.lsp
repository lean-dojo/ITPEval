;; Statement-only formalization of miniF2F artifact aime_1983_p2:
        ;; under the stated real interval hypotheses, the sum of three absolute values defining f(x) is at least 15.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime83p2-real-p (value) t)
(defstub aime83p2-zero () t)
(defstub aime83p2-one () t)
(defstub aime83p2-add (left right) t)
(defstub aime83p2-mul (left right) t)
(defstub aime83p2-neg (value) t)
(defstub aime83p2-inv (value) t)
(defstub aime83p2-lt (left right) t)
(defstub aime83p2-of-rational (value) t)

(defun aime83p2-sub (left right)
  (aime83p2-add left (aime83p2-neg right)))

(defun aime83p2-div (left right)
  (aime83p2-mul left (aime83p2-inv right)))

(defun aime83p2-le (left right)
  (or (equal left right) (aime83p2-lt left right)))

(defun aime83p2-nonnegative-p (value)
  (and (aime83p2-real-p value)
       (aime83p2-le (aime83p2-zero) value)))

(defun aime83p2-positive-p (value)
  (and (aime83p2-real-p value)
       (aime83p2-lt (aime83p2-zero) value)))

(defun aime83p2-abs (value)
  (if (aime83p2-lt value (aime83p2-zero))
      (aime83p2-neg value)
    value))

(defun aime83p2-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime83p2-one)
    (aime83p2-mul
     value
     (aime83p2-pow value (1- exponent)))))

(defun-sk aime83p2-field-laws-p ()
  (forall (x y z)
    (and
     (aime83p2-real-p (aime83p2-zero))
     (aime83p2-real-p (aime83p2-one))
     (not (equal (aime83p2-zero) (aime83p2-one)))
     (implies
      (aime83p2-real-p x)
      (and
       (aime83p2-real-p (aime83p2-neg x))
       (aime83p2-real-p (aime83p2-inv x))
       (equal (aime83p2-add x (aime83p2-zero)) x)
       (equal (aime83p2-add x (aime83p2-neg x))
              (aime83p2-zero))
       (equal (aime83p2-mul x (aime83p2-one)) x)
       (implies
        (not (equal x (aime83p2-zero)))
        (equal (aime83p2-mul x (aime83p2-inv x))
               (aime83p2-one)))))
     (equal (aime83p2-inv (aime83p2-zero))
            (aime83p2-zero))
     (implies
      (and (aime83p2-real-p x)
           (aime83p2-real-p y))
      (and
       (aime83p2-real-p (aime83p2-add x y))
       (aime83p2-real-p (aime83p2-mul x y))
       (equal (aime83p2-add x y)
              (aime83p2-add y x))
       (equal (aime83p2-mul x y)
              (aime83p2-mul y x))))
     (implies
      (and (aime83p2-real-p x)
           (aime83p2-real-p y)
           (aime83p2-real-p z))
      (and
       (equal (aime83p2-add (aime83p2-add x y) z)
              (aime83p2-add x (aime83p2-add y z)))
       (equal (aime83p2-mul (aime83p2-mul x y) z)
              (aime83p2-mul x (aime83p2-mul y z)))
       (equal (aime83p2-mul x (aime83p2-add y z))
              (aime83p2-add
               (aime83p2-mul x y)
               (aime83p2-mul x z))))))))

(defun-sk aime83p2-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime83p2-real-p x)
          (aime83p2-real-p y)
          (aime83p2-real-p z))
     (and
      (not (aime83p2-lt x x))
      (or (equal x y)
          (aime83p2-lt x y)
          (aime83p2-lt y x))
      (implies
       (and (aime83p2-lt x y)
            (aime83p2-lt y z))
       (aime83p2-lt x z))
      (implies
       (aime83p2-lt x y)
       (aime83p2-lt
        (aime83p2-add x z)
        (aime83p2-add y z)))
      (implies
       (and (aime83p2-lt (aime83p2-zero) x)
            (aime83p2-lt (aime83p2-zero) y))
       (aime83p2-lt
        (aime83p2-zero)
        (aime83p2-mul x y)))))))

(defun-sk aime83p2-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime83p2-real-p (aime83p2-of-rational a))
      (equal (aime83p2-of-rational 0) (aime83p2-zero))
      (equal (aime83p2-of-rational 1) (aime83p2-one))
      (equal
       (aime83p2-of-rational (+ a b))
       (aime83p2-add
        (aime83p2-of-rational a)
        (aime83p2-of-rational b)))
      (equal
       (aime83p2-of-rational (* a b))
       (aime83p2-mul
        (aime83p2-of-rational a)
        (aime83p2-of-rational b)))
      (equal
       (aime83p2-of-rational (- a))
       (aime83p2-neg (aime83p2-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime83p2-of-rational a)
        (aime83p2-of-rational b)))
      (iff
       (< a b)
       (aime83p2-lt
        (aime83p2-of-rational a)
        (aime83p2-of-rational b)))))))

(defun aime83p2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime83p2-real-p (car coefficients))
     (aime83p2-polynomial-p (cdr coefficients)))))

(defun aime83p2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime83p2-zero)
    (aime83p2-add
     (car coefficients)
     (aime83p2-mul
      x
      (aime83p2-polynomial-value
       (cdr coefficients) x)))))

(defun aime83p2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime83p2-leading-coefficient (cdr coefficients))))

(defun aime83p2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime83p2-leading-coefficient coefficients)
     (aime83p2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime83p2-square-root-exists-p (x)
  (exists (root)
    (and
     (aime83p2-nonnegative-p root)
     (equal (aime83p2-mul root root) x))))

(defun-sk aime83p2-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime83p2-nonnegative-p x)
     (aime83p2-square-root-exists-p x))))

(defun-sk aime83p2-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime83p2-real-p root)
     (equal
      (aime83p2-polynomial-value coefficients root)
      (aime83p2-zero)))))

(defun-sk aime83p2-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime83p2-polynomial-p coefficients)
      (aime83p2-odd-degree-p coefficients))
     (aime83p2-polynomial-root-exists-p coefficients))))

(defun aime83p2-real-closed-field-p ()
  (and
   (aime83p2-field-laws-p)
   (aime83p2-order-laws-p)
   (aime83p2-rational-laws-p)
   (aime83p2-lt (aime83p2-zero) (aime83p2-one))
   (aime83p2-nonnegative-square-roots-p)
   (aime83p2-odd-polynomial-roots-p)))

(defun aime83p2-principal-square-root-p (root value)
  (and
   (aime83p2-nonnegative-p root)
   (equal (aime83p2-mul root root) value)))

(defchoose aime83p2-sqrt (root) (value)
  (aime83p2-principal-square-root-p root value))

        (defun aime-1983-p2-statement (x p f-at-x)
  (implies
   (and
    (aime83p2-real-closed-field-p)
    (aime83p2-real-p x)
    (aime83p2-real-p p)
    (aime83p2-real-p f-at-x)
    (aime83p2-lt (aime83p2-zero) p)
    (aime83p2-lt p (aime83p2-of-rational 15))
    (aime83p2-le p x)
    (aime83p2-le x (aime83p2-of-rational 15))
    (equal
     f-at-x
     (aime83p2-add
      (aime83p2-add
       (aime83p2-abs (aime83p2-sub x p))
       (aime83p2-abs
        (aime83p2-sub x (aime83p2-of-rational 15))))
      (aime83p2-abs
       (aime83p2-sub
        (aime83p2-sub x p)
        (aime83p2-of-rational 15))))))
   (aime83p2-le
    (aime83p2-of-rational 15)
    f-at-x)))

        (value-triple :itpeval-statement-checked)
        :q
