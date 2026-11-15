;; Statement-only formalization of miniF2F artifact amc12b_2002_p19:
        ;; positive real a, b, c satisfying a(b+c)=152, b(c+a)=162, and c(a+b)=170 have product 720.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amcb02p19-real-p (value) t)
(defstub amcb02p19-zero () t)
(defstub amcb02p19-one () t)
(defstub amcb02p19-add (left right) t)
(defstub amcb02p19-mul (left right) t)
(defstub amcb02p19-neg (value) t)
(defstub amcb02p19-inv (value) t)
(defstub amcb02p19-lt (left right) t)
(defstub amcb02p19-of-rational (value) t)

(defun amcb02p19-sub (left right)
  (amcb02p19-add left (amcb02p19-neg right)))

(defun amcb02p19-div (left right)
  (amcb02p19-mul left (amcb02p19-inv right)))

(defun amcb02p19-le (left right)
  (or (equal left right) (amcb02p19-lt left right)))

(defun amcb02p19-nonnegative-p (value)
  (and (amcb02p19-real-p value)
       (amcb02p19-le (amcb02p19-zero) value)))

(defun amcb02p19-positive-p (value)
  (and (amcb02p19-real-p value)
       (amcb02p19-lt (amcb02p19-zero) value)))

(defun amcb02p19-abs (value)
  (if (amcb02p19-lt value (amcb02p19-zero))
      (amcb02p19-neg value)
    value))

(defun amcb02p19-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb02p19-one)
    (amcb02p19-mul
     value
     (amcb02p19-pow value (1- exponent)))))

(defun-sk amcb02p19-field-laws-p ()
  (forall (x y z)
    (and
     (amcb02p19-real-p (amcb02p19-zero))
     (amcb02p19-real-p (amcb02p19-one))
     (not (equal (amcb02p19-zero) (amcb02p19-one)))
     (implies
      (amcb02p19-real-p x)
      (and
       (amcb02p19-real-p (amcb02p19-neg x))
       (amcb02p19-real-p (amcb02p19-inv x))
       (equal (amcb02p19-add x (amcb02p19-zero)) x)
       (equal (amcb02p19-add x (amcb02p19-neg x))
              (amcb02p19-zero))
       (equal (amcb02p19-mul x (amcb02p19-one)) x)
       (implies
        (not (equal x (amcb02p19-zero)))
        (equal (amcb02p19-mul x (amcb02p19-inv x))
               (amcb02p19-one)))))
     (equal (amcb02p19-inv (amcb02p19-zero))
            (amcb02p19-zero))
     (implies
      (and (amcb02p19-real-p x)
           (amcb02p19-real-p y))
      (and
       (amcb02p19-real-p (amcb02p19-add x y))
       (amcb02p19-real-p (amcb02p19-mul x y))
       (equal (amcb02p19-add x y)
              (amcb02p19-add y x))
       (equal (amcb02p19-mul x y)
              (amcb02p19-mul y x))))
     (implies
      (and (amcb02p19-real-p x)
           (amcb02p19-real-p y)
           (amcb02p19-real-p z))
      (and
       (equal (amcb02p19-add (amcb02p19-add x y) z)
              (amcb02p19-add x (amcb02p19-add y z)))
       (equal (amcb02p19-mul (amcb02p19-mul x y) z)
              (amcb02p19-mul x (amcb02p19-mul y z)))
       (equal (amcb02p19-mul x (amcb02p19-add y z))
              (amcb02p19-add
               (amcb02p19-mul x y)
               (amcb02p19-mul x z))))))))

(defun-sk amcb02p19-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amcb02p19-real-p x)
          (amcb02p19-real-p y)
          (amcb02p19-real-p z))
     (and
      (not (amcb02p19-lt x x))
      (or (equal x y)
          (amcb02p19-lt x y)
          (amcb02p19-lt y x))
      (implies
       (and (amcb02p19-lt x y)
            (amcb02p19-lt y z))
       (amcb02p19-lt x z))
      (implies
       (amcb02p19-lt x y)
       (amcb02p19-lt
        (amcb02p19-add x z)
        (amcb02p19-add y z)))
      (implies
       (and (amcb02p19-lt (amcb02p19-zero) x)
            (amcb02p19-lt (amcb02p19-zero) y))
       (amcb02p19-lt
        (amcb02p19-zero)
        (amcb02p19-mul x y)))))))

(defun-sk amcb02p19-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amcb02p19-real-p (amcb02p19-of-rational a))
      (equal (amcb02p19-of-rational 0) (amcb02p19-zero))
      (equal (amcb02p19-of-rational 1) (amcb02p19-one))
      (equal
       (amcb02p19-of-rational (+ a b))
       (amcb02p19-add
        (amcb02p19-of-rational a)
        (amcb02p19-of-rational b)))
      (equal
       (amcb02p19-of-rational (* a b))
       (amcb02p19-mul
        (amcb02p19-of-rational a)
        (amcb02p19-of-rational b)))
      (equal
       (amcb02p19-of-rational (- a))
       (amcb02p19-neg (amcb02p19-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amcb02p19-of-rational a)
        (amcb02p19-of-rational b)))
      (iff
       (< a b)
       (amcb02p19-lt
        (amcb02p19-of-rational a)
        (amcb02p19-of-rational b)))))))

(defun amcb02p19-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amcb02p19-real-p (car coefficients))
     (amcb02p19-polynomial-p (cdr coefficients)))))

(defun amcb02p19-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amcb02p19-zero)
    (amcb02p19-add
     (car coefficients)
     (amcb02p19-mul
      x
      (amcb02p19-polynomial-value
       (cdr coefficients) x)))))

(defun amcb02p19-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amcb02p19-leading-coefficient (cdr coefficients))))

(defun amcb02p19-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amcb02p19-leading-coefficient coefficients)
     (amcb02p19-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amcb02p19-square-root-exists-p (x)
  (exists (root)
    (and
     (amcb02p19-nonnegative-p root)
     (equal (amcb02p19-mul root root) x))))

(defun-sk amcb02p19-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amcb02p19-nonnegative-p x)
     (amcb02p19-square-root-exists-p x))))

(defun-sk amcb02p19-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amcb02p19-real-p root)
     (equal
      (amcb02p19-polynomial-value coefficients root)
      (amcb02p19-zero)))))

(defun-sk amcb02p19-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amcb02p19-polynomial-p coefficients)
      (amcb02p19-odd-degree-p coefficients))
     (amcb02p19-polynomial-root-exists-p coefficients))))

(defun amcb02p19-real-closed-field-p ()
  (and
   (amcb02p19-field-laws-p)
   (amcb02p19-order-laws-p)
   (amcb02p19-rational-laws-p)
   (amcb02p19-lt (amcb02p19-zero) (amcb02p19-one))
   (amcb02p19-nonnegative-square-roots-p)
   (amcb02p19-odd-polynomial-roots-p)))

(defun amcb02p19-principal-square-root-p (root value)
  (and
   (amcb02p19-nonnegative-p root)
   (equal (amcb02p19-mul root root) value)))

(defchoose amcb02p19-sqrt (root) (value)
  (amcb02p19-principal-square-root-p root value))

        (defun amc12b-2002-p19-statement (a b c)
  (implies
   (and
    (amcb02p19-real-closed-field-p)
    (amcb02p19-positive-p a)
    (amcb02p19-positive-p b)
    (amcb02p19-positive-p c)
    (equal
     (amcb02p19-mul a (amcb02p19-add b c))
     (amcb02p19-of-rational 152))
    (equal
     (amcb02p19-mul b (amcb02p19-add c a))
     (amcb02p19-of-rational 162))
    (equal
     (amcb02p19-mul c (amcb02p19-add a b))
     (amcb02p19-of-rational 170)))
   (equal
    (amcb02p19-mul (amcb02p19-mul a b) c)
    (amcb02p19-of-rational 720))))

        (value-triple :itpeval-statement-checked)
        :q
