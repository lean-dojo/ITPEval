;; Statement-only formalization of miniF2F artifact amc12b_2021_p3:
        ;; the stated continued-fraction equation over the reals implies x = 3/4.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amcb21p3-real-p (value) t)
(defstub amcb21p3-zero () t)
(defstub amcb21p3-one () t)
(defstub amcb21p3-add (left right) t)
(defstub amcb21p3-mul (left right) t)
(defstub amcb21p3-neg (value) t)
(defstub amcb21p3-inv (value) t)
(defstub amcb21p3-lt (left right) t)
(defstub amcb21p3-of-rational (value) t)

(defun amcb21p3-sub (left right)
  (amcb21p3-add left (amcb21p3-neg right)))

(defun amcb21p3-div (left right)
  (amcb21p3-mul left (amcb21p3-inv right)))

(defun amcb21p3-le (left right)
  (or (equal left right) (amcb21p3-lt left right)))

(defun amcb21p3-nonnegative-p (value)
  (and (amcb21p3-real-p value)
       (amcb21p3-le (amcb21p3-zero) value)))

(defun amcb21p3-positive-p (value)
  (and (amcb21p3-real-p value)
       (amcb21p3-lt (amcb21p3-zero) value)))

(defun amcb21p3-abs (value)
  (if (amcb21p3-lt value (amcb21p3-zero))
      (amcb21p3-neg value)
    value))

(defun amcb21p3-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb21p3-one)
    (amcb21p3-mul
     value
     (amcb21p3-pow value (1- exponent)))))

(defun-sk amcb21p3-field-laws-p ()
  (forall (x y z)
    (and
     (amcb21p3-real-p (amcb21p3-zero))
     (amcb21p3-real-p (amcb21p3-one))
     (not (equal (amcb21p3-zero) (amcb21p3-one)))
     (implies
      (amcb21p3-real-p x)
      (and
       (amcb21p3-real-p (amcb21p3-neg x))
       (amcb21p3-real-p (amcb21p3-inv x))
       (equal (amcb21p3-add x (amcb21p3-zero)) x)
       (equal (amcb21p3-add x (amcb21p3-neg x))
              (amcb21p3-zero))
       (equal (amcb21p3-mul x (amcb21p3-one)) x)
       (implies
        (not (equal x (amcb21p3-zero)))
        (equal (amcb21p3-mul x (amcb21p3-inv x))
               (amcb21p3-one)))))
     (equal (amcb21p3-inv (amcb21p3-zero))
            (amcb21p3-zero))
     (implies
      (and (amcb21p3-real-p x)
           (amcb21p3-real-p y))
      (and
       (amcb21p3-real-p (amcb21p3-add x y))
       (amcb21p3-real-p (amcb21p3-mul x y))
       (equal (amcb21p3-add x y)
              (amcb21p3-add y x))
       (equal (amcb21p3-mul x y)
              (amcb21p3-mul y x))))
     (implies
      (and (amcb21p3-real-p x)
           (amcb21p3-real-p y)
           (amcb21p3-real-p z))
      (and
       (equal (amcb21p3-add (amcb21p3-add x y) z)
              (amcb21p3-add x (amcb21p3-add y z)))
       (equal (amcb21p3-mul (amcb21p3-mul x y) z)
              (amcb21p3-mul x (amcb21p3-mul y z)))
       (equal (amcb21p3-mul x (amcb21p3-add y z))
              (amcb21p3-add
               (amcb21p3-mul x y)
               (amcb21p3-mul x z))))))))

(defun-sk amcb21p3-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amcb21p3-real-p x)
          (amcb21p3-real-p y)
          (amcb21p3-real-p z))
     (and
      (not (amcb21p3-lt x x))
      (or (equal x y)
          (amcb21p3-lt x y)
          (amcb21p3-lt y x))
      (implies
       (and (amcb21p3-lt x y)
            (amcb21p3-lt y z))
       (amcb21p3-lt x z))
      (implies
       (amcb21p3-lt x y)
       (amcb21p3-lt
        (amcb21p3-add x z)
        (amcb21p3-add y z)))
      (implies
       (and (amcb21p3-lt (amcb21p3-zero) x)
            (amcb21p3-lt (amcb21p3-zero) y))
       (amcb21p3-lt
        (amcb21p3-zero)
        (amcb21p3-mul x y)))))))

(defun-sk amcb21p3-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amcb21p3-real-p (amcb21p3-of-rational a))
      (equal (amcb21p3-of-rational 0) (amcb21p3-zero))
      (equal (amcb21p3-of-rational 1) (amcb21p3-one))
      (equal
       (amcb21p3-of-rational (+ a b))
       (amcb21p3-add
        (amcb21p3-of-rational a)
        (amcb21p3-of-rational b)))
      (equal
       (amcb21p3-of-rational (* a b))
       (amcb21p3-mul
        (amcb21p3-of-rational a)
        (amcb21p3-of-rational b)))
      (equal
       (amcb21p3-of-rational (- a))
       (amcb21p3-neg (amcb21p3-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amcb21p3-of-rational a)
        (amcb21p3-of-rational b)))
      (iff
       (< a b)
       (amcb21p3-lt
        (amcb21p3-of-rational a)
        (amcb21p3-of-rational b)))))))

(defun amcb21p3-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amcb21p3-real-p (car coefficients))
     (amcb21p3-polynomial-p (cdr coefficients)))))

(defun amcb21p3-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amcb21p3-zero)
    (amcb21p3-add
     (car coefficients)
     (amcb21p3-mul
      x
      (amcb21p3-polynomial-value
       (cdr coefficients) x)))))

(defun amcb21p3-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amcb21p3-leading-coefficient (cdr coefficients))))

(defun amcb21p3-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amcb21p3-leading-coefficient coefficients)
     (amcb21p3-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amcb21p3-square-root-exists-p (x)
  (exists (root)
    (and
     (amcb21p3-nonnegative-p root)
     (equal (amcb21p3-mul root root) x))))

(defun-sk amcb21p3-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amcb21p3-nonnegative-p x)
     (amcb21p3-square-root-exists-p x))))

(defun-sk amcb21p3-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amcb21p3-real-p root)
     (equal
      (amcb21p3-polynomial-value coefficients root)
      (amcb21p3-zero)))))

(defun-sk amcb21p3-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amcb21p3-polynomial-p coefficients)
      (amcb21p3-odd-degree-p coefficients))
     (amcb21p3-polynomial-root-exists-p coefficients))))

(defun amcb21p3-real-closed-field-p ()
  (and
   (amcb21p3-field-laws-p)
   (amcb21p3-order-laws-p)
   (amcb21p3-rational-laws-p)
   (amcb21p3-lt (amcb21p3-zero) (amcb21p3-one))
   (amcb21p3-nonnegative-square-roots-p)
   (amcb21p3-odd-polynomial-roots-p)))

(defun amcb21p3-principal-square-root-p (root value)
  (and
   (amcb21p3-nonnegative-p root)
   (equal (amcb21p3-mul root root) value)))

(defchoose amcb21p3-sqrt (root) (value)
  (amcb21p3-principal-square-root-p root value))

        (defun amc12b-2021-p3-statement (x)
  (implies
   (and
    (amcb21p3-real-closed-field-p)
    (amcb21p3-real-p x)
    (equal
     (amcb21p3-add
      (amcb21p3-of-rational 2)
      (amcb21p3-div
       (amcb21p3-one)
       (amcb21p3-add
        (amcb21p3-one)
        (amcb21p3-div
         (amcb21p3-one)
         (amcb21p3-add
          (amcb21p3-of-rational 2)
          (amcb21p3-div
           (amcb21p3-of-rational 2)
           (amcb21p3-add
            (amcb21p3-of-rational 3)
            x)))))))
     (amcb21p3-of-rational 144/53)))
   (equal x (amcb21p3-of-rational 3/4))))

        (value-triple :itpeval-statement-checked)
        :q
