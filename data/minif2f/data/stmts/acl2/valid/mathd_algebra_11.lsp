;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_11:
;; for real numbers a and b, the stated unequal-denominator conditions and
;; (4*a + 3*b)/(a - 2*b) = 5 imply (a + 11*b)/(a - b) = 2. This file
;; contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier and
;; operations below present an Archimedean ordered field. All algebraic and
;; order laws remain explicit premises of the statement; DEFSTUB introduces
;; no laws, and no premise encodes this theorem's conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd11-real-p (value) t)
(defstub mathd11-zero () t)
(defstub mathd11-one () t)
(defstub mathd11-add (left right) t)
(defstub mathd11-mul (left right) t)
(defstub mathd11-neg (value) t)
(defstub mathd11-inv (value) t)
(defstub mathd11-lt (left right) t)

(defun mathd11-sub (left right)
  (mathd11-add left (mathd11-neg right)))

(defun mathd11-div (left right)
  (mathd11-mul left (mathd11-inv right)))

(defun mathd11-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd11-zero)
    (mathd11-add
     (mathd11-one)
     (mathd11-natural (1- n)))))

(defun-sk mathd11-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y))
     (and
      (mathd11-real-p (mathd11-add x y))
      (mathd11-real-p (mathd11-mul x y))))
    (implies
     (mathd11-real-p x)
     (and
      (mathd11-real-p (mathd11-neg x))
      (mathd11-real-p (mathd11-inv x))))

    ;; Additive commutative group.
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y)
          (mathd11-real-p z))
     (equal
      (mathd11-add (mathd11-add x y) z)
      (mathd11-add x (mathd11-add y z))))
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y))
     (equal (mathd11-add x y)
            (mathd11-add y x)))
    (implies
     (mathd11-real-p x)
     (and
      (equal (mathd11-add x (mathd11-zero)) x)
      (equal
       (mathd11-add x (mathd11-neg x))
       (mathd11-zero))))

    ;; Multiplicative commutative group away from zero.
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y)
          (mathd11-real-p z))
     (equal
      (mathd11-mul (mathd11-mul x y) z)
      (mathd11-mul x (mathd11-mul y z))))
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y))
     (equal (mathd11-mul x y)
            (mathd11-mul y x)))
    (implies
     (mathd11-real-p x)
     (equal (mathd11-mul x (mathd11-one)) x))
    (implies
     (and
      (mathd11-real-p x)
      (not (equal x (mathd11-zero))))
     (equal
      (mathd11-mul x (mathd11-inv x))
      (mathd11-one)))
    (equal (mathd11-inv (mathd11-zero))
           (mathd11-zero))

    ;; Distributivity.
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y)
          (mathd11-real-p z))
     (equal
      (mathd11-mul x (mathd11-add y z))
      (mathd11-add
       (mathd11-mul x y)
       (mathd11-mul x z)))))))

(defun-sk mathd11-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (mathd11-real-p x)
     (not (mathd11-lt x x)))
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y))
     (or (mathd11-lt x y)
         (equal x y)
         (mathd11-lt y x)))
    (implies
     (and
      (mathd11-real-p x)
      (mathd11-real-p y)
      (mathd11-real-p z)
      (mathd11-lt x y)
      (mathd11-lt y z))
     (mathd11-lt x z))

    ;; Compatibility with addition and positive multiplication.
    (implies
     (and (mathd11-real-p x)
          (mathd11-real-p y)
          (mathd11-real-p z))
     (iff
      (mathd11-lt x y)
      (mathd11-lt
       (mathd11-add x z)
       (mathd11-add y z))))
    (implies
     (and
      (mathd11-real-p x)
      (mathd11-real-p y)
      (mathd11-lt (mathd11-zero) x)
      (mathd11-lt (mathd11-zero) y))
     (mathd11-lt
      (mathd11-zero)
      (mathd11-mul x y))))))

(defun-sk mathd11-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd11-lt x (mathd11-natural n)))))

(defun-sk mathd11-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd11-real-p x)
    (mathd11-natural-bound-exists-p x))))

(defun mathd11-real-field-p ()
  (and
   (mathd11-real-p (mathd11-zero))
   (mathd11-real-p (mathd11-one))
   (not (equal (mathd11-zero) (mathd11-one)))
   (mathd11-lt (mathd11-zero) (mathd11-one))
   (mathd11-field-laws-p)
   (mathd11-order-laws-p)
   (mathd11-archimedean-p)))

(defun mathd-algebra-11-statement (a b)
  (implies
   (and
    (mathd11-real-field-p)
    (mathd11-real-p a)
    (mathd11-real-p b)
    (not (equal a b))
    (not
     (equal
      a
      (mathd11-mul (mathd11-natural 2) b)))
    (equal
     (mathd11-div
      (mathd11-add
       (mathd11-mul (mathd11-natural 4) a)
       (mathd11-mul (mathd11-natural 3) b))
      (mathd11-sub
       a
       (mathd11-mul (mathd11-natural 2) b)))
     (mathd11-natural 5)))
   (equal
    (mathd11-div
     (mathd11-add
      a
      (mathd11-mul (mathd11-natural 11) b))
     (mathd11-sub a b))
    (mathd11-natural 2))))

(value-triple :itpeval-statement-checked)
:q
