;; Statement-only formalization of miniF2F artifact amc12b_2003_p9:
        ;; for a real affine function f(x)=a*x+b, f(6)-f(2)=12 implies f(12)-f(2)=30.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amcb03p9-real-p (value) t)
(defstub amcb03p9-zero () t)
(defstub amcb03p9-one () t)
(defstub amcb03p9-add (left right) t)
(defstub amcb03p9-mul (left right) t)
(defstub amcb03p9-neg (value) t)
(defstub amcb03p9-inv (value) t)
(defstub amcb03p9-lt (left right) t)
(defstub amcb03p9-of-rational (value) t)

(defun amcb03p9-sub (left right)
  (amcb03p9-add left (amcb03p9-neg right)))

(defun amcb03p9-div (left right)
  (amcb03p9-mul left (amcb03p9-inv right)))

(defun amcb03p9-le (left right)
  (or (equal left right) (amcb03p9-lt left right)))

(defun amcb03p9-nonnegative-p (value)
  (and (amcb03p9-real-p value)
       (amcb03p9-le (amcb03p9-zero) value)))

(defun amcb03p9-positive-p (value)
  (and (amcb03p9-real-p value)
       (amcb03p9-lt (amcb03p9-zero) value)))

(defun amcb03p9-abs (value)
  (if (amcb03p9-lt value (amcb03p9-zero))
      (amcb03p9-neg value)
    value))

(defun amcb03p9-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb03p9-one)
    (amcb03p9-mul
     value
     (amcb03p9-pow value (1- exponent)))))

(defun-sk amcb03p9-field-laws-p ()
  (forall (x y z)
    (and
     (amcb03p9-real-p (amcb03p9-zero))
     (amcb03p9-real-p (amcb03p9-one))
     (not (equal (amcb03p9-zero) (amcb03p9-one)))
     (implies
      (amcb03p9-real-p x)
      (and
       (amcb03p9-real-p (amcb03p9-neg x))
       (amcb03p9-real-p (amcb03p9-inv x))
       (equal (amcb03p9-add x (amcb03p9-zero)) x)
       (equal (amcb03p9-add x (amcb03p9-neg x))
              (amcb03p9-zero))
       (equal (amcb03p9-mul x (amcb03p9-one)) x)
       (implies
        (not (equal x (amcb03p9-zero)))
        (equal (amcb03p9-mul x (amcb03p9-inv x))
               (amcb03p9-one)))))
     (equal (amcb03p9-inv (amcb03p9-zero))
            (amcb03p9-zero))
     (implies
      (and (amcb03p9-real-p x)
           (amcb03p9-real-p y))
      (and
       (amcb03p9-real-p (amcb03p9-add x y))
       (amcb03p9-real-p (amcb03p9-mul x y))
       (equal (amcb03p9-add x y)
              (amcb03p9-add y x))
       (equal (amcb03p9-mul x y)
              (amcb03p9-mul y x))))
     (implies
      (and (amcb03p9-real-p x)
           (amcb03p9-real-p y)
           (amcb03p9-real-p z))
      (and
       (equal (amcb03p9-add (amcb03p9-add x y) z)
              (amcb03p9-add x (amcb03p9-add y z)))
       (equal (amcb03p9-mul (amcb03p9-mul x y) z)
              (amcb03p9-mul x (amcb03p9-mul y z)))
       (equal (amcb03p9-mul x (amcb03p9-add y z))
              (amcb03p9-add
               (amcb03p9-mul x y)
               (amcb03p9-mul x z))))))))

(defun-sk amcb03p9-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amcb03p9-real-p x)
          (amcb03p9-real-p y)
          (amcb03p9-real-p z))
     (and
      (not (amcb03p9-lt x x))
      (or (equal x y)
          (amcb03p9-lt x y)
          (amcb03p9-lt y x))
      (implies
       (and (amcb03p9-lt x y)
            (amcb03p9-lt y z))
       (amcb03p9-lt x z))
      (implies
       (amcb03p9-lt x y)
       (amcb03p9-lt
        (amcb03p9-add x z)
        (amcb03p9-add y z)))
      (implies
       (and (amcb03p9-lt (amcb03p9-zero) x)
            (amcb03p9-lt (amcb03p9-zero) y))
       (amcb03p9-lt
        (amcb03p9-zero)
        (amcb03p9-mul x y)))))))

(defun-sk amcb03p9-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amcb03p9-real-p (amcb03p9-of-rational a))
      (equal (amcb03p9-of-rational 0) (amcb03p9-zero))
      (equal (amcb03p9-of-rational 1) (amcb03p9-one))
      (equal
       (amcb03p9-of-rational (+ a b))
       (amcb03p9-add
        (amcb03p9-of-rational a)
        (amcb03p9-of-rational b)))
      (equal
       (amcb03p9-of-rational (* a b))
       (amcb03p9-mul
        (amcb03p9-of-rational a)
        (amcb03p9-of-rational b)))
      (equal
       (amcb03p9-of-rational (- a))
       (amcb03p9-neg (amcb03p9-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amcb03p9-of-rational a)
        (amcb03p9-of-rational b)))
      (iff
       (< a b)
       (amcb03p9-lt
        (amcb03p9-of-rational a)
        (amcb03p9-of-rational b)))))))

(defun amcb03p9-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amcb03p9-real-p (car coefficients))
     (amcb03p9-polynomial-p (cdr coefficients)))))

(defun amcb03p9-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amcb03p9-zero)
    (amcb03p9-add
     (car coefficients)
     (amcb03p9-mul
      x
      (amcb03p9-polynomial-value
       (cdr coefficients) x)))))

(defun amcb03p9-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amcb03p9-leading-coefficient (cdr coefficients))))

(defun amcb03p9-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amcb03p9-leading-coefficient coefficients)
     (amcb03p9-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amcb03p9-square-root-exists-p (x)
  (exists (root)
    (and
     (amcb03p9-nonnegative-p root)
     (equal (amcb03p9-mul root root) x))))

(defun-sk amcb03p9-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amcb03p9-nonnegative-p x)
     (amcb03p9-square-root-exists-p x))))

(defun-sk amcb03p9-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amcb03p9-real-p root)
     (equal
      (amcb03p9-polynomial-value coefficients root)
      (amcb03p9-zero)))))

(defun-sk amcb03p9-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amcb03p9-polynomial-p coefficients)
      (amcb03p9-odd-degree-p coefficients))
     (amcb03p9-polynomial-root-exists-p coefficients))))

(defun amcb03p9-real-closed-field-p ()
  (and
   (amcb03p9-field-laws-p)
   (amcb03p9-order-laws-p)
   (amcb03p9-rational-laws-p)
   (amcb03p9-lt (amcb03p9-zero) (amcb03p9-one))
   (amcb03p9-nonnegative-square-roots-p)
   (amcb03p9-odd-polynomial-roots-p)))

(defun amcb03p9-principal-square-root-p (root value)
  (and
   (amcb03p9-nonnegative-p root)
   (equal (amcb03p9-mul root root) value)))

(defchoose amcb03p9-sqrt (root) (value)
  (amcb03p9-principal-square-root-p root value))

        (defun amcb03p9-affine (a b x)
  (amcb03p9-add (amcb03p9-mul a x) b))

(defun amc12b-2003-p9-statement (a b)
  (implies
   (and
    (amcb03p9-real-closed-field-p)
    (amcb03p9-real-p a)
    (amcb03p9-real-p b)
    (equal
     (amcb03p9-sub
      (amcb03p9-affine
       a b (amcb03p9-of-rational 6))
      (amcb03p9-affine
       a b (amcb03p9-of-rational 2)))
     (amcb03p9-of-rational 12)))
   (equal
    (amcb03p9-sub
     (amcb03p9-affine
      a b (amcb03p9-of-rational 12))
     (amcb03p9-affine
      a b (amcb03p9-of-rational 2)))
    (amcb03p9-of-rational 30))))

        (value-triple :itpeval-statement-checked)
        :q
