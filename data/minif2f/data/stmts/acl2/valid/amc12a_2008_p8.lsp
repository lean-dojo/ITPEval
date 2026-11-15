;; Statement-only formalization of miniF2F artifact amc12a_2008_p8:
        ;; positive real x,y with y^3=1 and 6x^2=2(6y^2) satisfy x^3=2*sqrt(2).
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca08p8-real-p (value) t)
(defstub amca08p8-zero () t)
(defstub amca08p8-one () t)
(defstub amca08p8-add (left right) t)
(defstub amca08p8-mul (left right) t)
(defstub amca08p8-neg (value) t)
(defstub amca08p8-inv (value) t)
(defstub amca08p8-lt (left right) t)
(defstub amca08p8-of-rational (value) t)

(defun amca08p8-sub (left right)
  (amca08p8-add left (amca08p8-neg right)))

(defun amca08p8-div (left right)
  (amca08p8-mul left (amca08p8-inv right)))

(defun amca08p8-le (left right)
  (or (equal left right) (amca08p8-lt left right)))

(defun amca08p8-nonnegative-p (value)
  (and (amca08p8-real-p value)
       (amca08p8-le (amca08p8-zero) value)))

(defun amca08p8-positive-p (value)
  (and (amca08p8-real-p value)
       (amca08p8-lt (amca08p8-zero) value)))

(defun amca08p8-abs (value)
  (if (amca08p8-lt value (amca08p8-zero))
      (amca08p8-neg value)
    value))

(defun amca08p8-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca08p8-one)
    (amca08p8-mul
     value
     (amca08p8-pow value (1- exponent)))))

(defun-sk amca08p8-field-laws-p ()
  (forall (x y z)
    (and
     (amca08p8-real-p (amca08p8-zero))
     (amca08p8-real-p (amca08p8-one))
     (not (equal (amca08p8-zero) (amca08p8-one)))
     (implies
      (amca08p8-real-p x)
      (and
       (amca08p8-real-p (amca08p8-neg x))
       (amca08p8-real-p (amca08p8-inv x))
       (equal (amca08p8-add x (amca08p8-zero)) x)
       (equal (amca08p8-add x (amca08p8-neg x))
              (amca08p8-zero))
       (equal (amca08p8-mul x (amca08p8-one)) x)
       (implies
        (not (equal x (amca08p8-zero)))
        (equal (amca08p8-mul x (amca08p8-inv x))
               (amca08p8-one)))))
     (equal (amca08p8-inv (amca08p8-zero))
            (amca08p8-zero))
     (implies
      (and (amca08p8-real-p x)
           (amca08p8-real-p y))
      (and
       (amca08p8-real-p (amca08p8-add x y))
       (amca08p8-real-p (amca08p8-mul x y))
       (equal (amca08p8-add x y)
              (amca08p8-add y x))
       (equal (amca08p8-mul x y)
              (amca08p8-mul y x))))
     (implies
      (and (amca08p8-real-p x)
           (amca08p8-real-p y)
           (amca08p8-real-p z))
      (and
       (equal (amca08p8-add (amca08p8-add x y) z)
              (amca08p8-add x (amca08p8-add y z)))
       (equal (amca08p8-mul (amca08p8-mul x y) z)
              (amca08p8-mul x (amca08p8-mul y z)))
       (equal (amca08p8-mul x (amca08p8-add y z))
              (amca08p8-add
               (amca08p8-mul x y)
               (amca08p8-mul x z))))))))

(defun-sk amca08p8-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca08p8-real-p x)
          (amca08p8-real-p y)
          (amca08p8-real-p z))
     (and
      (not (amca08p8-lt x x))
      (or (equal x y)
          (amca08p8-lt x y)
          (amca08p8-lt y x))
      (implies
       (and (amca08p8-lt x y)
            (amca08p8-lt y z))
       (amca08p8-lt x z))
      (implies
       (amca08p8-lt x y)
       (amca08p8-lt
        (amca08p8-add x z)
        (amca08p8-add y z)))
      (implies
       (and (amca08p8-lt (amca08p8-zero) x)
            (amca08p8-lt (amca08p8-zero) y))
       (amca08p8-lt
        (amca08p8-zero)
        (amca08p8-mul x y)))))))

(defun-sk amca08p8-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca08p8-real-p (amca08p8-of-rational a))
      (equal (amca08p8-of-rational 0) (amca08p8-zero))
      (equal (amca08p8-of-rational 1) (amca08p8-one))
      (equal
       (amca08p8-of-rational (+ a b))
       (amca08p8-add
        (amca08p8-of-rational a)
        (amca08p8-of-rational b)))
      (equal
       (amca08p8-of-rational (* a b))
       (amca08p8-mul
        (amca08p8-of-rational a)
        (amca08p8-of-rational b)))
      (equal
       (amca08p8-of-rational (- a))
       (amca08p8-neg (amca08p8-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca08p8-of-rational a)
        (amca08p8-of-rational b)))
      (iff
       (< a b)
       (amca08p8-lt
        (amca08p8-of-rational a)
        (amca08p8-of-rational b)))))))

(defun amca08p8-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca08p8-real-p (car coefficients))
     (amca08p8-polynomial-p (cdr coefficients)))))

(defun amca08p8-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca08p8-zero)
    (amca08p8-add
     (car coefficients)
     (amca08p8-mul
      x
      (amca08p8-polynomial-value
       (cdr coefficients) x)))))

(defun amca08p8-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca08p8-leading-coefficient (cdr coefficients))))

(defun amca08p8-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca08p8-leading-coefficient coefficients)
     (amca08p8-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca08p8-square-root-exists-p (x)
  (exists (root)
    (and
     (amca08p8-nonnegative-p root)
     (equal (amca08p8-mul root root) x))))

(defun-sk amca08p8-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca08p8-nonnegative-p x)
     (amca08p8-square-root-exists-p x))))

(defun-sk amca08p8-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca08p8-real-p root)
     (equal
      (amca08p8-polynomial-value coefficients root)
      (amca08p8-zero)))))

(defun-sk amca08p8-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca08p8-polynomial-p coefficients)
      (amca08p8-odd-degree-p coefficients))
     (amca08p8-polynomial-root-exists-p coefficients))))

(defun amca08p8-real-closed-field-p ()
  (and
   (amca08p8-field-laws-p)
   (amca08p8-order-laws-p)
   (amca08p8-rational-laws-p)
   (amca08p8-lt (amca08p8-zero) (amca08p8-one))
   (amca08p8-nonnegative-square-roots-p)
   (amca08p8-odd-polynomial-roots-p)))

(defun amca08p8-principal-square-root-p (root value)
  (and
   (amca08p8-nonnegative-p root)
   (equal (amca08p8-mul root root) value)))

(defchoose amca08p8-sqrt (root) (value)
  (amca08p8-principal-square-root-p root value))

        (defun amc12a-2008-p8-statement (x y)
  (implies
   (and
    (amca08p8-real-closed-field-p)
    (amca08p8-positive-p x)
    (amca08p8-positive-p y)
    (equal (amca08p8-pow y 3) (amca08p8-one))
    (equal
     (amca08p8-mul
      (amca08p8-of-rational 6)
      (amca08p8-pow x 2))
     (amca08p8-mul
      (amca08p8-of-rational 2)
      (amca08p8-mul
       (amca08p8-of-rational 6)
       (amca08p8-pow y 2)))))
   (equal
    (amca08p8-pow x 3)
    (amca08p8-mul
     (amca08p8-of-rational 2)
     (amca08p8-sqrt (amca08p8-of-rational 2))))))

        (value-triple :itpeval-statement-checked)
        :q
