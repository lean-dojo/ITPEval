;; Statement-only formalization of miniF2F artifact amc12a_2009_p9:
        ;; the two source definitions of the same real function imply a+b+c=2.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca09p9-real-p (value) t)
(defstub amca09p9-zero () t)
(defstub amca09p9-one () t)
(defstub amca09p9-add (left right) t)
(defstub amca09p9-mul (left right) t)
(defstub amca09p9-neg (value) t)
(defstub amca09p9-inv (value) t)
(defstub amca09p9-lt (left right) t)
(defstub amca09p9-of-rational (value) t)

(defun amca09p9-sub (left right)
  (amca09p9-add left (amca09p9-neg right)))

(defun amca09p9-div (left right)
  (amca09p9-mul left (amca09p9-inv right)))

(defun amca09p9-le (left right)
  (or (equal left right) (amca09p9-lt left right)))

(defun amca09p9-nonnegative-p (value)
  (and (amca09p9-real-p value)
       (amca09p9-le (amca09p9-zero) value)))

(defun amca09p9-positive-p (value)
  (and (amca09p9-real-p value)
       (amca09p9-lt (amca09p9-zero) value)))

(defun amca09p9-abs (value)
  (if (amca09p9-lt value (amca09p9-zero))
      (amca09p9-neg value)
    value))

(defun amca09p9-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca09p9-one)
    (amca09p9-mul
     value
     (amca09p9-pow value (1- exponent)))))

(defun-sk amca09p9-field-laws-p ()
  (forall (x y z)
    (and
     (amca09p9-real-p (amca09p9-zero))
     (amca09p9-real-p (amca09p9-one))
     (not (equal (amca09p9-zero) (amca09p9-one)))
     (implies
      (amca09p9-real-p x)
      (and
       (amca09p9-real-p (amca09p9-neg x))
       (amca09p9-real-p (amca09p9-inv x))
       (equal (amca09p9-add x (amca09p9-zero)) x)
       (equal (amca09p9-add x (amca09p9-neg x))
              (amca09p9-zero))
       (equal (amca09p9-mul x (amca09p9-one)) x)
       (implies
        (not (equal x (amca09p9-zero)))
        (equal (amca09p9-mul x (amca09p9-inv x))
               (amca09p9-one)))))
     (equal (amca09p9-inv (amca09p9-zero))
            (amca09p9-zero))
     (implies
      (and (amca09p9-real-p x)
           (amca09p9-real-p y))
      (and
       (amca09p9-real-p (amca09p9-add x y))
       (amca09p9-real-p (amca09p9-mul x y))
       (equal (amca09p9-add x y)
              (amca09p9-add y x))
       (equal (amca09p9-mul x y)
              (amca09p9-mul y x))))
     (implies
      (and (amca09p9-real-p x)
           (amca09p9-real-p y)
           (amca09p9-real-p z))
      (and
       (equal (amca09p9-add (amca09p9-add x y) z)
              (amca09p9-add x (amca09p9-add y z)))
       (equal (amca09p9-mul (amca09p9-mul x y) z)
              (amca09p9-mul x (amca09p9-mul y z)))
       (equal (amca09p9-mul x (amca09p9-add y z))
              (amca09p9-add
               (amca09p9-mul x y)
               (amca09p9-mul x z))))))))

(defun-sk amca09p9-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca09p9-real-p x)
          (amca09p9-real-p y)
          (amca09p9-real-p z))
     (and
      (not (amca09p9-lt x x))
      (or (equal x y)
          (amca09p9-lt x y)
          (amca09p9-lt y x))
      (implies
       (and (amca09p9-lt x y)
            (amca09p9-lt y z))
       (amca09p9-lt x z))
      (implies
       (amca09p9-lt x y)
       (amca09p9-lt
        (amca09p9-add x z)
        (amca09p9-add y z)))
      (implies
       (and (amca09p9-lt (amca09p9-zero) x)
            (amca09p9-lt (amca09p9-zero) y))
       (amca09p9-lt
        (amca09p9-zero)
        (amca09p9-mul x y)))))))

(defun-sk amca09p9-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca09p9-real-p (amca09p9-of-rational a))
      (equal (amca09p9-of-rational 0) (amca09p9-zero))
      (equal (amca09p9-of-rational 1) (amca09p9-one))
      (equal
       (amca09p9-of-rational (+ a b))
       (amca09p9-add
        (amca09p9-of-rational a)
        (amca09p9-of-rational b)))
      (equal
       (amca09p9-of-rational (* a b))
       (amca09p9-mul
        (amca09p9-of-rational a)
        (amca09p9-of-rational b)))
      (equal
       (amca09p9-of-rational (- a))
       (amca09p9-neg (amca09p9-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca09p9-of-rational a)
        (amca09p9-of-rational b)))
      (iff
       (< a b)
       (amca09p9-lt
        (amca09p9-of-rational a)
        (amca09p9-of-rational b)))))))

(defun amca09p9-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca09p9-real-p (car coefficients))
     (amca09p9-polynomial-p (cdr coefficients)))))

(defun amca09p9-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca09p9-zero)
    (amca09p9-add
     (car coefficients)
     (amca09p9-mul
      x
      (amca09p9-polynomial-value
       (cdr coefficients) x)))))

(defun amca09p9-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca09p9-leading-coefficient (cdr coefficients))))

(defun amca09p9-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca09p9-leading-coefficient coefficients)
     (amca09p9-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca09p9-square-root-exists-p (x)
  (exists (root)
    (and
     (amca09p9-nonnegative-p root)
     (equal (amca09p9-mul root root) x))))

(defun-sk amca09p9-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca09p9-nonnegative-p x)
     (amca09p9-square-root-exists-p x))))

(defun-sk amca09p9-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca09p9-real-p root)
     (equal
      (amca09p9-polynomial-value coefficients root)
      (amca09p9-zero)))))

(defun-sk amca09p9-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca09p9-polynomial-p coefficients)
      (amca09p9-odd-degree-p coefficients))
     (amca09p9-polynomial-root-exists-p coefficients))))

(defun amca09p9-real-closed-field-p ()
  (and
   (amca09p9-field-laws-p)
   (amca09p9-order-laws-p)
   (amca09p9-rational-laws-p)
   (amca09p9-lt (amca09p9-zero) (amca09p9-one))
   (amca09p9-nonnegative-square-roots-p)
   (amca09p9-odd-polynomial-roots-p)))

(defun amca09p9-principal-square-root-p (root value)
  (and
   (amca09p9-nonnegative-p root)
   (equal (amca09p9-mul root root) value)))

(defchoose amca09p9-sqrt (root) (value)
  (amca09p9-principal-square-root-p root value))

        (defun-sk amca09p9-definition-compatibility-p (a b c)
  (forall (x)
    (implies
     (amca09p9-real-p x)
     (equal
      (amca09p9-add
       (amca09p9-add
        (amca09p9-mul
         a
         (amca09p9-pow
          (amca09p9-add x (amca09p9-of-rational 3))
          2))
        (amca09p9-mul
         b
         (amca09p9-add x (amca09p9-of-rational 3))))
       c)
      (amca09p9-add
       (amca09p9-add
        (amca09p9-mul
         (amca09p9-of-rational 3)
         (amca09p9-pow x 2))
        (amca09p9-mul
         (amca09p9-of-rational 7) x))
       (amca09p9-of-rational 4))))))

(defun amc12a-2009-p9-statement (a b c)
  (implies
   (and
    (amca09p9-real-closed-field-p)
    (amca09p9-real-p a)
    (amca09p9-real-p b)
    (amca09p9-real-p c)
    (amca09p9-definition-compatibility-p a b c))
   (equal
    (amca09p9-add (amca09p9-add a b) c)
    (amca09p9-of-rational 2))))

        (value-triple :itpeval-statement-checked)
        :q
