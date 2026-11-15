;; Statement-only formalization of miniF2F artifact imo_1964_p2:
        ;; positive side lengths satisfying the strict triangle inequalities obey the stated cubic inequality.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub imo64p2-real-p (value) t)
(defstub imo64p2-zero () t)
(defstub imo64p2-one () t)
(defstub imo64p2-add (left right) t)
(defstub imo64p2-mul (left right) t)
(defstub imo64p2-neg (value) t)
(defstub imo64p2-inv (value) t)
(defstub imo64p2-lt (left right) t)
(defstub imo64p2-of-rational (value) t)

(defun imo64p2-sub (left right)
  (imo64p2-add left (imo64p2-neg right)))

(defun imo64p2-div (left right)
  (imo64p2-mul left (imo64p2-inv right)))

(defun imo64p2-le (left right)
  (or (equal left right) (imo64p2-lt left right)))

(defun imo64p2-nonnegative-p (value)
  (and (imo64p2-real-p value)
       (imo64p2-le (imo64p2-zero) value)))

(defun imo64p2-positive-p (value)
  (and (imo64p2-real-p value)
       (imo64p2-lt (imo64p2-zero) value)))

(defun imo64p2-abs (value)
  (if (imo64p2-lt value (imo64p2-zero))
      (imo64p2-neg value)
    value))

(defun imo64p2-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (imo64p2-one)
    (imo64p2-mul
     value
     (imo64p2-pow value (1- exponent)))))

(defun-sk imo64p2-field-laws-p ()
  (forall (x y z)
    (and
     (imo64p2-real-p (imo64p2-zero))
     (imo64p2-real-p (imo64p2-one))
     (not (equal (imo64p2-zero) (imo64p2-one)))
     (implies
      (imo64p2-real-p x)
      (and
       (imo64p2-real-p (imo64p2-neg x))
       (imo64p2-real-p (imo64p2-inv x))
       (equal (imo64p2-add x (imo64p2-zero)) x)
       (equal (imo64p2-add x (imo64p2-neg x))
              (imo64p2-zero))
       (equal (imo64p2-mul x (imo64p2-one)) x)
       (implies
        (not (equal x (imo64p2-zero)))
        (equal (imo64p2-mul x (imo64p2-inv x))
               (imo64p2-one)))))
     (equal (imo64p2-inv (imo64p2-zero))
            (imo64p2-zero))
     (implies
      (and (imo64p2-real-p x)
           (imo64p2-real-p y))
      (and
       (imo64p2-real-p (imo64p2-add x y))
       (imo64p2-real-p (imo64p2-mul x y))
       (equal (imo64p2-add x y)
              (imo64p2-add y x))
       (equal (imo64p2-mul x y)
              (imo64p2-mul y x))))
     (implies
      (and (imo64p2-real-p x)
           (imo64p2-real-p y)
           (imo64p2-real-p z))
      (and
       (equal (imo64p2-add (imo64p2-add x y) z)
              (imo64p2-add x (imo64p2-add y z)))
       (equal (imo64p2-mul (imo64p2-mul x y) z)
              (imo64p2-mul x (imo64p2-mul y z)))
       (equal (imo64p2-mul x (imo64p2-add y z))
              (imo64p2-add
               (imo64p2-mul x y)
               (imo64p2-mul x z))))))))

(defun-sk imo64p2-order-laws-p ()
  (forall (x y z)
    (implies
     (and (imo64p2-real-p x)
          (imo64p2-real-p y)
          (imo64p2-real-p z))
     (and
      (not (imo64p2-lt x x))
      (or (equal x y)
          (imo64p2-lt x y)
          (imo64p2-lt y x))
      (implies
       (and (imo64p2-lt x y)
            (imo64p2-lt y z))
       (imo64p2-lt x z))
      (implies
       (imo64p2-lt x y)
       (imo64p2-lt
        (imo64p2-add x z)
        (imo64p2-add y z)))
      (implies
       (and (imo64p2-lt (imo64p2-zero) x)
            (imo64p2-lt (imo64p2-zero) y))
       (imo64p2-lt
        (imo64p2-zero)
        (imo64p2-mul x y)))))))

(defun-sk imo64p2-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (imo64p2-real-p (imo64p2-of-rational a))
      (equal (imo64p2-of-rational 0) (imo64p2-zero))
      (equal (imo64p2-of-rational 1) (imo64p2-one))
      (equal
       (imo64p2-of-rational (+ a b))
       (imo64p2-add
        (imo64p2-of-rational a)
        (imo64p2-of-rational b)))
      (equal
       (imo64p2-of-rational (* a b))
       (imo64p2-mul
        (imo64p2-of-rational a)
        (imo64p2-of-rational b)))
      (equal
       (imo64p2-of-rational (- a))
       (imo64p2-neg (imo64p2-of-rational a)))
      (iff
       (equal a b)
       (equal
        (imo64p2-of-rational a)
        (imo64p2-of-rational b)))
      (iff
       (< a b)
       (imo64p2-lt
        (imo64p2-of-rational a)
        (imo64p2-of-rational b)))))))

(defun imo64p2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (imo64p2-real-p (car coefficients))
     (imo64p2-polynomial-p (cdr coefficients)))))

(defun imo64p2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (imo64p2-zero)
    (imo64p2-add
     (car coefficients)
     (imo64p2-mul
      x
      (imo64p2-polynomial-value
       (cdr coefficients) x)))))

(defun imo64p2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (imo64p2-leading-coefficient (cdr coefficients))))

(defun imo64p2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (imo64p2-leading-coefficient coefficients)
     (imo64p2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk imo64p2-square-root-exists-p (x)
  (exists (root)
    (and
     (imo64p2-nonnegative-p root)
     (equal (imo64p2-mul root root) x))))

(defun-sk imo64p2-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (imo64p2-nonnegative-p x)
     (imo64p2-square-root-exists-p x))))

(defun-sk imo64p2-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (imo64p2-real-p root)
     (equal
      (imo64p2-polynomial-value coefficients root)
      (imo64p2-zero)))))

(defun-sk imo64p2-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (imo64p2-polynomial-p coefficients)
      (imo64p2-odd-degree-p coefficients))
     (imo64p2-polynomial-root-exists-p coefficients))))

(defun imo64p2-real-closed-field-p ()
  (and
   (imo64p2-field-laws-p)
   (imo64p2-order-laws-p)
   (imo64p2-rational-laws-p)
   (imo64p2-lt (imo64p2-zero) (imo64p2-one))
   (imo64p2-nonnegative-square-roots-p)
   (imo64p2-odd-polynomial-roots-p)))

(defun imo64p2-principal-square-root-p (root value)
  (and
   (imo64p2-nonnegative-p root)
   (equal (imo64p2-mul root root) value)))

(defchoose imo64p2-sqrt (root) (value)
  (imo64p2-principal-square-root-p root value))

        (defun imo-1964-p2-statement (a b c)
  (implies
   (and
    (imo64p2-real-closed-field-p)
    (imo64p2-positive-p a)
    (imo64p2-positive-p b)
    (imo64p2-positive-p c)
    (imo64p2-lt c (imo64p2-add a b))
    (imo64p2-lt b (imo64p2-add a c))
    (imo64p2-lt a (imo64p2-add b c)))
   (imo64p2-le
    (imo64p2-add
     (imo64p2-add
      (imo64p2-mul
       (imo64p2-pow a 2)
       (imo64p2-sub (imo64p2-add b c) a))
      (imo64p2-mul
       (imo64p2-pow b 2)
       (imo64p2-sub (imo64p2-add c a) b)))
     (imo64p2-mul
      (imo64p2-pow c 2)
      (imo64p2-sub (imo64p2-add a b) c)))
    (imo64p2-mul
     (imo64p2-of-rational 3)
     (imo64p2-mul (imo64p2-mul a b) c)))))

        (value-triple :itpeval-statement-checked)
        :q
