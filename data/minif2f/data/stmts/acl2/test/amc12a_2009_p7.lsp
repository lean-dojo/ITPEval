;; Statement-only formalization of miniF2F artifact amc12a_2009_p7:
        ;; a real arithmetic sequence satisfying the three initial-value equations and a(n)=2009 must have n=502.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca09p7-real-p (value) t)
(defstub amca09p7-zero () t)
(defstub amca09p7-one () t)
(defstub amca09p7-add (left right) t)
(defstub amca09p7-mul (left right) t)
(defstub amca09p7-neg (value) t)
(defstub amca09p7-inv (value) t)
(defstub amca09p7-lt (left right) t)
(defstub amca09p7-of-rational (value) t)

(defun amca09p7-sub (left right)
  (amca09p7-add left (amca09p7-neg right)))

(defun amca09p7-div (left right)
  (amca09p7-mul left (amca09p7-inv right)))

(defun amca09p7-le (left right)
  (or (equal left right) (amca09p7-lt left right)))

(defun amca09p7-nonnegative-p (value)
  (and (amca09p7-real-p value)
       (amca09p7-le (amca09p7-zero) value)))

(defun amca09p7-positive-p (value)
  (and (amca09p7-real-p value)
       (amca09p7-lt (amca09p7-zero) value)))

(defun amca09p7-abs (value)
  (if (amca09p7-lt value (amca09p7-zero))
      (amca09p7-neg value)
    value))

(defun amca09p7-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca09p7-one)
    (amca09p7-mul
     value
     (amca09p7-pow value (1- exponent)))))

(defun-sk amca09p7-field-laws-p ()
  (forall (x y z)
    (and
     (amca09p7-real-p (amca09p7-zero))
     (amca09p7-real-p (amca09p7-one))
     (not (equal (amca09p7-zero) (amca09p7-one)))
     (implies
      (amca09p7-real-p x)
      (and
       (amca09p7-real-p (amca09p7-neg x))
       (amca09p7-real-p (amca09p7-inv x))
       (equal (amca09p7-add x (amca09p7-zero)) x)
       (equal (amca09p7-add x (amca09p7-neg x))
              (amca09p7-zero))
       (equal (amca09p7-mul x (amca09p7-one)) x)
       (implies
        (not (equal x (amca09p7-zero)))
        (equal (amca09p7-mul x (amca09p7-inv x))
               (amca09p7-one)))))
     (equal (amca09p7-inv (amca09p7-zero))
            (amca09p7-zero))
     (implies
      (and (amca09p7-real-p x)
           (amca09p7-real-p y))
      (and
       (amca09p7-real-p (amca09p7-add x y))
       (amca09p7-real-p (amca09p7-mul x y))
       (equal (amca09p7-add x y)
              (amca09p7-add y x))
       (equal (amca09p7-mul x y)
              (amca09p7-mul y x))))
     (implies
      (and (amca09p7-real-p x)
           (amca09p7-real-p y)
           (amca09p7-real-p z))
      (and
       (equal (amca09p7-add (amca09p7-add x y) z)
              (amca09p7-add x (amca09p7-add y z)))
       (equal (amca09p7-mul (amca09p7-mul x y) z)
              (amca09p7-mul x (amca09p7-mul y z)))
       (equal (amca09p7-mul x (amca09p7-add y z))
              (amca09p7-add
               (amca09p7-mul x y)
               (amca09p7-mul x z))))))))

(defun-sk amca09p7-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca09p7-real-p x)
          (amca09p7-real-p y)
          (amca09p7-real-p z))
     (and
      (not (amca09p7-lt x x))
      (or (equal x y)
          (amca09p7-lt x y)
          (amca09p7-lt y x))
      (implies
       (and (amca09p7-lt x y)
            (amca09p7-lt y z))
       (amca09p7-lt x z))
      (implies
       (amca09p7-lt x y)
       (amca09p7-lt
        (amca09p7-add x z)
        (amca09p7-add y z)))
      (implies
       (and (amca09p7-lt (amca09p7-zero) x)
            (amca09p7-lt (amca09p7-zero) y))
       (amca09p7-lt
        (amca09p7-zero)
        (amca09p7-mul x y)))))))

(defun-sk amca09p7-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca09p7-real-p (amca09p7-of-rational a))
      (equal (amca09p7-of-rational 0) (amca09p7-zero))
      (equal (amca09p7-of-rational 1) (amca09p7-one))
      (equal
       (amca09p7-of-rational (+ a b))
       (amca09p7-add
        (amca09p7-of-rational a)
        (amca09p7-of-rational b)))
      (equal
       (amca09p7-of-rational (* a b))
       (amca09p7-mul
        (amca09p7-of-rational a)
        (amca09p7-of-rational b)))
      (equal
       (amca09p7-of-rational (- a))
       (amca09p7-neg (amca09p7-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca09p7-of-rational a)
        (amca09p7-of-rational b)))
      (iff
       (< a b)
       (amca09p7-lt
        (amca09p7-of-rational a)
        (amca09p7-of-rational b)))))))

(defun amca09p7-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca09p7-real-p (car coefficients))
     (amca09p7-polynomial-p (cdr coefficients)))))

(defun amca09p7-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca09p7-zero)
    (amca09p7-add
     (car coefficients)
     (amca09p7-mul
      x
      (amca09p7-polynomial-value
       (cdr coefficients) x)))))

(defun amca09p7-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca09p7-leading-coefficient (cdr coefficients))))

(defun amca09p7-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca09p7-leading-coefficient coefficients)
     (amca09p7-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca09p7-square-root-exists-p (x)
  (exists (root)
    (and
     (amca09p7-nonnegative-p root)
     (equal (amca09p7-mul root root) x))))

(defun-sk amca09p7-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca09p7-nonnegative-p x)
     (amca09p7-square-root-exists-p x))))

(defun-sk amca09p7-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca09p7-real-p root)
     (equal
      (amca09p7-polynomial-value coefficients root)
      (amca09p7-zero)))))

(defun-sk amca09p7-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca09p7-polynomial-p coefficients)
      (amca09p7-odd-degree-p coefficients))
     (amca09p7-polynomial-root-exists-p coefficients))))

(defun amca09p7-real-closed-field-p ()
  (and
   (amca09p7-field-laws-p)
   (amca09p7-order-laws-p)
   (amca09p7-rational-laws-p)
   (amca09p7-lt (amca09p7-zero) (amca09p7-one))
   (amca09p7-nonnegative-square-roots-p)
   (amca09p7-odd-polynomial-roots-p)))

(defun amca09p7-principal-square-root-p (root value)
  (and
   (amca09p7-nonnegative-p root)
   (equal (amca09p7-mul root root) value)))

(defchoose amca09p7-sqrt (root) (value)
  (amca09p7-principal-square-root-p root value))

        (defun amca09p7-sequence-value (initial difference index)
  (amca09p7-add
   initial
   (amca09p7-mul
    (amca09p7-of-rational index)
    difference)))

(defun amc12a-2009-p7-statement
    (x n initial difference)
  (implies
   (and
    (amca09p7-real-closed-field-p)
    (amca09p7-real-p x)
    (natp n)
    (amca09p7-real-p initial)
    (amca09p7-real-p difference)
    (equal
     (amca09p7-sequence-value initial difference 1)
     (amca09p7-sub
      (amca09p7-mul (amca09p7-of-rational 2) x)
      (amca09p7-of-rational 3)))
    (equal
     (amca09p7-sequence-value initial difference 2)
     (amca09p7-sub
      (amca09p7-mul (amca09p7-of-rational 5) x)
      (amca09p7-of-rational 11)))
    (equal
     (amca09p7-sequence-value initial difference 3)
     (amca09p7-add
      (amca09p7-mul (amca09p7-of-rational 3) x)
      (amca09p7-one)))
    (equal
     (amca09p7-sequence-value initial difference n)
     (amca09p7-of-rational 2009)))
   (equal n 502)))

        (value-triple :itpeval-statement-checked)
        :q
