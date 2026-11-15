;; Statement-only formalization of miniF2F artifact amc12a_2009_p5:
        ;; the stated cubic identity for a real x implies x^3 = 125.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca09p5-real-p (value) t)
(defstub amca09p5-zero () t)
(defstub amca09p5-one () t)
(defstub amca09p5-add (left right) t)
(defstub amca09p5-mul (left right) t)
(defstub amca09p5-neg (value) t)
(defstub amca09p5-inv (value) t)
(defstub amca09p5-lt (left right) t)
(defstub amca09p5-of-rational (value) t)

(defun amca09p5-sub (left right)
  (amca09p5-add left (amca09p5-neg right)))

(defun amca09p5-div (left right)
  (amca09p5-mul left (amca09p5-inv right)))

(defun amca09p5-le (left right)
  (or (equal left right) (amca09p5-lt left right)))

(defun amca09p5-nonnegative-p (value)
  (and (amca09p5-real-p value)
       (amca09p5-le (amca09p5-zero) value)))

(defun amca09p5-positive-p (value)
  (and (amca09p5-real-p value)
       (amca09p5-lt (amca09p5-zero) value)))

(defun amca09p5-abs (value)
  (if (amca09p5-lt value (amca09p5-zero))
      (amca09p5-neg value)
    value))

(defun amca09p5-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca09p5-one)
    (amca09p5-mul
     value
     (amca09p5-pow value (1- exponent)))))

(defun-sk amca09p5-field-laws-p ()
  (forall (x y z)
    (and
     (amca09p5-real-p (amca09p5-zero))
     (amca09p5-real-p (amca09p5-one))
     (not (equal (amca09p5-zero) (amca09p5-one)))
     (implies
      (amca09p5-real-p x)
      (and
       (amca09p5-real-p (amca09p5-neg x))
       (amca09p5-real-p (amca09p5-inv x))
       (equal (amca09p5-add x (amca09p5-zero)) x)
       (equal (amca09p5-add x (amca09p5-neg x))
              (amca09p5-zero))
       (equal (amca09p5-mul x (amca09p5-one)) x)
       (implies
        (not (equal x (amca09p5-zero)))
        (equal (amca09p5-mul x (amca09p5-inv x))
               (amca09p5-one)))))
     (equal (amca09p5-inv (amca09p5-zero))
            (amca09p5-zero))
     (implies
      (and (amca09p5-real-p x)
           (amca09p5-real-p y))
      (and
       (amca09p5-real-p (amca09p5-add x y))
       (amca09p5-real-p (amca09p5-mul x y))
       (equal (amca09p5-add x y)
              (amca09p5-add y x))
       (equal (amca09p5-mul x y)
              (amca09p5-mul y x))))
     (implies
      (and (amca09p5-real-p x)
           (amca09p5-real-p y)
           (amca09p5-real-p z))
      (and
       (equal (amca09p5-add (amca09p5-add x y) z)
              (amca09p5-add x (amca09p5-add y z)))
       (equal (amca09p5-mul (amca09p5-mul x y) z)
              (amca09p5-mul x (amca09p5-mul y z)))
       (equal (amca09p5-mul x (amca09p5-add y z))
              (amca09p5-add
               (amca09p5-mul x y)
               (amca09p5-mul x z))))))))

(defun-sk amca09p5-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca09p5-real-p x)
          (amca09p5-real-p y)
          (amca09p5-real-p z))
     (and
      (not (amca09p5-lt x x))
      (or (equal x y)
          (amca09p5-lt x y)
          (amca09p5-lt y x))
      (implies
       (and (amca09p5-lt x y)
            (amca09p5-lt y z))
       (amca09p5-lt x z))
      (implies
       (amca09p5-lt x y)
       (amca09p5-lt
        (amca09p5-add x z)
        (amca09p5-add y z)))
      (implies
       (and (amca09p5-lt (amca09p5-zero) x)
            (amca09p5-lt (amca09p5-zero) y))
       (amca09p5-lt
        (amca09p5-zero)
        (amca09p5-mul x y)))))))

(defun-sk amca09p5-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca09p5-real-p (amca09p5-of-rational a))
      (equal (amca09p5-of-rational 0) (amca09p5-zero))
      (equal (amca09p5-of-rational 1) (amca09p5-one))
      (equal
       (amca09p5-of-rational (+ a b))
       (amca09p5-add
        (amca09p5-of-rational a)
        (amca09p5-of-rational b)))
      (equal
       (amca09p5-of-rational (* a b))
       (amca09p5-mul
        (amca09p5-of-rational a)
        (amca09p5-of-rational b)))
      (equal
       (amca09p5-of-rational (- a))
       (amca09p5-neg (amca09p5-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca09p5-of-rational a)
        (amca09p5-of-rational b)))
      (iff
       (< a b)
       (amca09p5-lt
        (amca09p5-of-rational a)
        (amca09p5-of-rational b)))))))

(defun amca09p5-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca09p5-real-p (car coefficients))
     (amca09p5-polynomial-p (cdr coefficients)))))

(defun amca09p5-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca09p5-zero)
    (amca09p5-add
     (car coefficients)
     (amca09p5-mul
      x
      (amca09p5-polynomial-value
       (cdr coefficients) x)))))

(defun amca09p5-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca09p5-leading-coefficient (cdr coefficients))))

(defun amca09p5-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca09p5-leading-coefficient coefficients)
     (amca09p5-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca09p5-square-root-exists-p (x)
  (exists (root)
    (and
     (amca09p5-nonnegative-p root)
     (equal (amca09p5-mul root root) x))))

(defun-sk amca09p5-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca09p5-nonnegative-p x)
     (amca09p5-square-root-exists-p x))))

(defun-sk amca09p5-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca09p5-real-p root)
     (equal
      (amca09p5-polynomial-value coefficients root)
      (amca09p5-zero)))))

(defun-sk amca09p5-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca09p5-polynomial-p coefficients)
      (amca09p5-odd-degree-p coefficients))
     (amca09p5-polynomial-root-exists-p coefficients))))

(defun amca09p5-real-closed-field-p ()
  (and
   (amca09p5-field-laws-p)
   (amca09p5-order-laws-p)
   (amca09p5-rational-laws-p)
   (amca09p5-lt (amca09p5-zero) (amca09p5-one))
   (amca09p5-nonnegative-square-roots-p)
   (amca09p5-odd-polynomial-roots-p)))

(defun amca09p5-principal-square-root-p (root value)
  (and
   (amca09p5-nonnegative-p root)
   (equal (amca09p5-mul root root) value)))

(defchoose amca09p5-sqrt (root) (value)
  (amca09p5-principal-square-root-p root value))

        (defun amc12a-2009-p5-statement (x)
  (implies
   (and
    (amca09p5-real-closed-field-p)
    (amca09p5-real-p x)
    (equal
     (amca09p5-sub
      (amca09p5-pow x 3)
      (amca09p5-mul
       (amca09p5-mul
        (amca09p5-add x (amca09p5-one))
        (amca09p5-sub x (amca09p5-one)))
       x))
     (amca09p5-of-rational 5)))
   (equal
    (amca09p5-pow x 3)
    (amca09p5-of-rational 125))))

        (value-triple :itpeval-statement-checked)
        :q
