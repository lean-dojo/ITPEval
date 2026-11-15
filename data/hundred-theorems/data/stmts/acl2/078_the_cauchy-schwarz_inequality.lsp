;; Statement-only formalization of Hundred Theorems artifact 078, "The
;; Cauchy-Schwarz Inequality": in an inner-product space over an arbitrary
;; strict ordered field, <x,y>^2 is at most <x,x><y,y>.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's conservative generic function symbols represent the scalar field,
;; vector space, and inner product.  Every required law remains an explicit
;; hypothesis of the benchmark statement.
(defstub ht078-scalar-p (x) t)
(defstub ht078-add-op (x y) t)
(defstub ht078-multiply-op (x y) t)
(defstub ht078-negate-op (x) t)
(defstub ht078-inverse-op (x) t)
(defstub ht078-less-op (x y) t)
(defstub ht078-vector-p (x) t)
(defstub ht078-vector-add-op (x y) t)
(defstub ht078-vector-negate-op (x) t)
(defstub ht078-scalar-multiply-op (a x) t)
(defstub ht078-inner-op (x y) t)

(defun ht078-scalar-member-p (x)
  (if (ht078-scalar-p x) t nil))

(defun ht078-add (x y)
  (ht078-add-op x y))

(defun ht078-mul (x y)
  (ht078-multiply-op x y))

(defun ht078-neg (x)
  (ht078-negate-op x))

(defun ht078-inv (x)
  (ht078-inverse-op x))

(defun ht078-less (x y)
  (if (ht078-less-op x y) t nil))

(defun ht078-vector-member-p (x)
  (if (ht078-vector-p x) t nil))

(defun ht078-vadd (x y)
  (ht078-vector-add-op x y))

(defun ht078-vneg (x)
  (ht078-vector-negate-op x))

(defun ht078-smul (a x)
  (ht078-scalar-multiply-op a x))

(defun ht078-inner (x y)
  (ht078-inner-op x y))

(defun-sk ht078-field-laws-p (zero one)
  (forall (a b c)
    (implies
     (and
      (ht078-scalar-member-p a)
      (ht078-scalar-member-p b)
      (ht078-scalar-member-p c))
     (and
      (ht078-scalar-member-p (ht078-add a b))
      (ht078-scalar-member-p (ht078-mul a b))
      (ht078-scalar-member-p (ht078-neg a))
      (ht078-scalar-member-p (ht078-inv a))
      (equal (ht078-add (ht078-add a b) c)
             (ht078-add a (ht078-add b c)))
      (equal (ht078-add a b) (ht078-add b a))
      (equal (ht078-add a zero) a)
      (equal (ht078-add a (ht078-neg a)) zero)
      (equal (ht078-mul (ht078-mul a b) c)
             (ht078-mul a (ht078-mul b c)))
      (equal (ht078-mul a b) (ht078-mul b a))
      (equal (ht078-mul a one) a)
      (equal (ht078-inv zero) zero)
      (implies
       (not (equal a zero))
       (equal (ht078-mul a (ht078-inv a)) one))
      (equal
       (ht078-mul a (ht078-add b c))
       (ht078-add (ht078-mul a b)
                  (ht078-mul a c)))))))

(defun-sk ht078-order-laws-p (zero)
  (forall (a b c)
    (implies
     (and
      (ht078-scalar-member-p a)
      (ht078-scalar-member-p b)
      (ht078-scalar-member-p c))
     (and
      (not (ht078-less a a))
      (or (equal a b)
          (ht078-less a b)
          (ht078-less b a))
      (implies
       (and (ht078-less a b)
            (ht078-less b c))
       (ht078-less a c))
      (implies
       (ht078-less a b)
       (ht078-less (ht078-add a c)
                   (ht078-add b c)))
      (implies
       (and (ht078-less zero a)
            (ht078-less zero b))
       (ht078-less zero (ht078-mul a b)))))))

(defun ht078-ordered-field-p (zero one)
  (and
   (ht078-scalar-member-p zero)
   (ht078-scalar-member-p one)
   (not (equal zero one))
   (ht078-less zero one)
   (ht078-field-laws-p zero one)
   (ht078-order-laws-p zero)))

(defun-sk ht078-vector-space-laws-p (zero one vector-zero)
  (forall (a b x y z)
    (implies
     (and
      (ht078-scalar-member-p a)
      (ht078-scalar-member-p b)
      (ht078-vector-member-p x)
      (ht078-vector-member-p y)
      (ht078-vector-member-p z))
     (and
      (ht078-vector-member-p (ht078-vadd x y))
      (ht078-vector-member-p (ht078-vneg x))
      (ht078-vector-member-p (ht078-smul a x))
      (equal (ht078-vadd (ht078-vadd x y) z)
             (ht078-vadd x (ht078-vadd y z)))
      (equal (ht078-vadd x y) (ht078-vadd y x))
      (equal (ht078-vadd x vector-zero) x)
      (equal (ht078-vadd x (ht078-vneg x)) vector-zero)
      (equal (ht078-smul one x) x)
      (equal (ht078-smul (ht078-mul a b) x)
             (ht078-smul a (ht078-smul b x)))
      (equal (ht078-smul a (ht078-vadd x y))
             (ht078-vadd (ht078-smul a x)
                         (ht078-smul a y)))
      (equal (ht078-smul (ht078-add a b) x)
             (ht078-vadd (ht078-smul a x)
                         (ht078-smul b x)))
      (equal (ht078-smul zero x) vector-zero)))))

(defun-sk ht078-inner-product-laws-p (zero)
  (forall (a x y z)
    (implies
     (and
      (ht078-scalar-member-p a)
      (ht078-vector-member-p x)
      (ht078-vector-member-p y)
      (ht078-vector-member-p z))
     (and
      (ht078-scalar-member-p (ht078-inner x y))
      (equal (ht078-inner x y)
             (ht078-inner y x))
      (equal (ht078-inner (ht078-vadd x y) z)
             (ht078-add (ht078-inner x z)
                        (ht078-inner y z)))
      (equal (ht078-inner (ht078-smul a x) y)
             (ht078-mul a (ht078-inner x y)))
      (not (ht078-less (ht078-inner x x) zero))
      (implies
       (equal (ht078-inner x x) zero)
       (equal x (ht078-smul zero x)))))))

(defun ht078-inner-product-space-p (zero one vector-zero)
  (and
   (ht078-ordered-field-p zero one)
   (ht078-vector-member-p vector-zero)
   (ht078-vector-space-laws-p zero one vector-zero)
   (ht078-inner-product-laws-p zero)))

(defun hundred-theorems-078-cauchy-schwarz-statement
    (zero one vector-zero x y)
  (implies
   (and
    (ht078-inner-product-space-p zero one vector-zero)
    (ht078-vector-member-p x)
    (ht078-vector-member-p y))
   (not
    (ht078-less
     (ht078-mul (ht078-inner x x)
                (ht078-inner y y))
     (ht078-mul (ht078-inner x y)
                (ht078-inner x y))))))

(value-triple :itpeval-statement-checked)
:q
