;; Statement-only formalization of miniF2F artifact amc12a_2020_p25:
        ;; a finite set exactly enumerating the real solutions of the source floor equation and summing to 420 forces the reduced rational parameter's numerator and denominator to sum to 929.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca20p25-real-p (value) t)
(defstub amca20p25-zero () t)
(defstub amca20p25-one () t)
(defstub amca20p25-add (left right) t)
(defstub amca20p25-mul (left right) t)
(defstub amca20p25-neg (value) t)
(defstub amca20p25-inv (value) t)
(defstub amca20p25-lt (left right) t)
(defstub amca20p25-of-rational (value) t)

(defun amca20p25-sub (left right)
  (amca20p25-add left (amca20p25-neg right)))

(defun amca20p25-div (left right)
  (amca20p25-mul left (amca20p25-inv right)))

(defun amca20p25-le (left right)
  (or (equal left right) (amca20p25-lt left right)))

(defun amca20p25-nonnegative-p (value)
  (and (amca20p25-real-p value)
       (amca20p25-le (amca20p25-zero) value)))

(defun amca20p25-positive-p (value)
  (and (amca20p25-real-p value)
       (amca20p25-lt (amca20p25-zero) value)))

(defun amca20p25-abs (value)
  (if (amca20p25-lt value (amca20p25-zero))
      (amca20p25-neg value)
    value))

(defun amca20p25-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca20p25-one)
    (amca20p25-mul
     value
     (amca20p25-pow value (1- exponent)))))

(defun-sk amca20p25-field-laws-p ()
  (forall (x y z)
    (and
     (amca20p25-real-p (amca20p25-zero))
     (amca20p25-real-p (amca20p25-one))
     (not (equal (amca20p25-zero) (amca20p25-one)))
     (implies
      (amca20p25-real-p x)
      (and
       (amca20p25-real-p (amca20p25-neg x))
       (amca20p25-real-p (amca20p25-inv x))
       (equal (amca20p25-add x (amca20p25-zero)) x)
       (equal (amca20p25-add x (amca20p25-neg x))
              (amca20p25-zero))
       (equal (amca20p25-mul x (amca20p25-one)) x)
       (implies
        (not (equal x (amca20p25-zero)))
        (equal (amca20p25-mul x (amca20p25-inv x))
               (amca20p25-one)))))
     (equal (amca20p25-inv (amca20p25-zero))
            (amca20p25-zero))
     (implies
      (and (amca20p25-real-p x)
           (amca20p25-real-p y))
      (and
       (amca20p25-real-p (amca20p25-add x y))
       (amca20p25-real-p (amca20p25-mul x y))
       (equal (amca20p25-add x y)
              (amca20p25-add y x))
       (equal (amca20p25-mul x y)
              (amca20p25-mul y x))))
     (implies
      (and (amca20p25-real-p x)
           (amca20p25-real-p y)
           (amca20p25-real-p z))
      (and
       (equal (amca20p25-add (amca20p25-add x y) z)
              (amca20p25-add x (amca20p25-add y z)))
       (equal (amca20p25-mul (amca20p25-mul x y) z)
              (amca20p25-mul x (amca20p25-mul y z)))
       (equal (amca20p25-mul x (amca20p25-add y z))
              (amca20p25-add
               (amca20p25-mul x y)
               (amca20p25-mul x z))))))))

(defun-sk amca20p25-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca20p25-real-p x)
          (amca20p25-real-p y)
          (amca20p25-real-p z))
     (and
      (not (amca20p25-lt x x))
      (or (equal x y)
          (amca20p25-lt x y)
          (amca20p25-lt y x))
      (implies
       (and (amca20p25-lt x y)
            (amca20p25-lt y z))
       (amca20p25-lt x z))
      (implies
       (amca20p25-lt x y)
       (amca20p25-lt
        (amca20p25-add x z)
        (amca20p25-add y z)))
      (implies
       (and (amca20p25-lt (amca20p25-zero) x)
            (amca20p25-lt (amca20p25-zero) y))
       (amca20p25-lt
        (amca20p25-zero)
        (amca20p25-mul x y)))))))

(defun-sk amca20p25-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca20p25-real-p (amca20p25-of-rational a))
      (equal (amca20p25-of-rational 0) (amca20p25-zero))
      (equal (amca20p25-of-rational 1) (amca20p25-one))
      (equal
       (amca20p25-of-rational (+ a b))
       (amca20p25-add
        (amca20p25-of-rational a)
        (amca20p25-of-rational b)))
      (equal
       (amca20p25-of-rational (* a b))
       (amca20p25-mul
        (amca20p25-of-rational a)
        (amca20p25-of-rational b)))
      (equal
       (amca20p25-of-rational (- a))
       (amca20p25-neg (amca20p25-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca20p25-of-rational a)
        (amca20p25-of-rational b)))
      (iff
       (< a b)
       (amca20p25-lt
        (amca20p25-of-rational a)
        (amca20p25-of-rational b)))))))

(defun amca20p25-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca20p25-real-p (car coefficients))
     (amca20p25-polynomial-p (cdr coefficients)))))

(defun amca20p25-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca20p25-zero)
    (amca20p25-add
     (car coefficients)
     (amca20p25-mul
      x
      (amca20p25-polynomial-value
       (cdr coefficients) x)))))

(defun amca20p25-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca20p25-leading-coefficient (cdr coefficients))))

(defun amca20p25-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca20p25-leading-coefficient coefficients)
     (amca20p25-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca20p25-square-root-exists-p (x)
  (exists (root)
    (and
     (amca20p25-nonnegative-p root)
     (equal (amca20p25-mul root root) x))))

(defun-sk amca20p25-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca20p25-nonnegative-p x)
     (amca20p25-square-root-exists-p x))))

(defun-sk amca20p25-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca20p25-real-p root)
     (equal
      (amca20p25-polynomial-value coefficients root)
      (amca20p25-zero)))))

(defun-sk amca20p25-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca20p25-polynomial-p coefficients)
      (amca20p25-odd-degree-p coefficients))
     (amca20p25-polynomial-root-exists-p coefficients))))

(defun amca20p25-real-closed-field-p ()
  (and
   (amca20p25-field-laws-p)
   (amca20p25-order-laws-p)
   (amca20p25-rational-laws-p)
   (amca20p25-lt (amca20p25-zero) (amca20p25-one))
   (amca20p25-nonnegative-square-roots-p)
   (amca20p25-odd-polynomial-roots-p)))

(defun amca20p25-principal-square-root-p (root value)
  (and
   (amca20p25-nonnegative-p root)
   (equal (amca20p25-mul root root) value)))

(defchoose amca20p25-sqrt (root) (value)
  (amca20p25-principal-square-root-p root value))

        (defstub amca20p25-floor (value) t)

(defun-sk amca20p25-floor-laws-p ()
  (forall (x)
    (implies
     (amca20p25-real-p x)
     (and
      (integerp (amca20p25-floor x))
      (amca20p25-le
       (amca20p25-of-rational
        (amca20p25-floor x))
       x)
      (amca20p25-lt
       x
       (amca20p25-of-rational
        (+ 1 (amca20p25-floor x))))))))

(defun amca20p25-real-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (amca20p25-real-p (car values))
     (amca20p25-real-list-p (cdr values)))))

(defun amca20p25-no-duplicates-p (values)
  (if (endp values)
      t
    (and
     (not (member-equal (car values) (cdr values)))
     (amca20p25-no-duplicates-p (cdr values)))))

(defun amca20p25-equation-p (a x)
  (let ((floor-x
         (amca20p25-of-rational
          (amca20p25-floor x))))
    (equal
     (amca20p25-mul
      floor-x
      (amca20p25-sub x floor-x))
     (amca20p25-mul
      (amca20p25-of-rational a)
      (amca20p25-pow x 2)))))

(defun-sk amca20p25-exact-solution-set-p (a solutions)
  (forall (x)
    (implies
     (amca20p25-real-p x)
     (iff
      (member-equal x solutions)
      (amca20p25-equation-p a x)))))

(defun amca20p25-sum (values)
  (if (endp values)
      (amca20p25-zero)
    (amca20p25-add
     (car values)
     (amca20p25-sum (cdr values)))))

(defun amc12a-2020-p25-statement (a solutions)
  (implies
   (and
    (amca20p25-real-closed-field-p)
    (amca20p25-floor-laws-p)
    (rationalp a)
    (true-listp solutions)
    (amca20p25-real-list-p solutions)
    (amca20p25-no-duplicates-p solutions)
    (amca20p25-exact-solution-set-p a solutions)
    (equal
     (amca20p25-sum solutions)
     (amca20p25-of-rational 420)))
   (equal
    (+ (denominator a) (numerator a))
    929)))

        (value-triple :itpeval-statement-checked)
        :q
