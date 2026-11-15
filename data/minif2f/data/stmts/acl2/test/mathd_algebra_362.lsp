;; Statement-only formalization of miniF2F artifact mathd_algebra_362:
;; for real a and b, the equations a^2*b^3=32/27 and
;; a/b^3=27/4 imply a+b=8/3. This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, and order below present an Archimedean
;; ordered field. Every law is an explicit premise; DEFSTUB introduces no
;; law, and no premise assumes the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd362-real-p (value) t)
(defstub mathd362-zero () t)
(defstub mathd362-one () t)
(defstub mathd362-add (left right) t)
(defstub mathd362-mul (left right) t)
(defstub mathd362-neg (value) t)
(defstub mathd362-inv (value) t)
(defstub mathd362-lt (left right) t)
(defstub mathd362-of-rational (value) t)

(defun mathd362-div (left right)
  (mathd362-mul left (mathd362-inv right)))

(defun mathd362-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd362-zero)
    (mathd362-add
     (mathd362-one)
     (mathd362-natural (1- n)))))

(defun mathd362-pow (value exponent)
  (declare (xargs :guard (natp exponent)))
  (if (zp exponent)
      (mathd362-one)
    (mathd362-mul
     value
     (mathd362-pow value (1- exponent)))))

(defun-sk mathd362-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd362-real-p x)
          (mathd362-real-p y))
     (and
      (mathd362-real-p (mathd362-add x y))
      (mathd362-real-p (mathd362-mul x y))))
    (implies
     (mathd362-real-p x)
     (and
      (mathd362-real-p (mathd362-neg x))
      (mathd362-real-p (mathd362-inv x))))
    (implies
     (and
      (mathd362-real-p x)
      (mathd362-real-p y)
      (mathd362-real-p z))
     (equal
      (mathd362-add (mathd362-add x y) z)
      (mathd362-add x (mathd362-add y z))))
    (implies
     (and (mathd362-real-p x)
          (mathd362-real-p y))
     (equal (mathd362-add x y)
            (mathd362-add y x)))
    (implies
     (mathd362-real-p x)
     (and
      (equal (mathd362-add x (mathd362-zero)) x)
      (equal
       (mathd362-add x (mathd362-neg x))
       (mathd362-zero))))
    (implies
     (and
      (mathd362-real-p x)
      (mathd362-real-p y)
      (mathd362-real-p z))
     (equal
      (mathd362-mul (mathd362-mul x y) z)
      (mathd362-mul x (mathd362-mul y z))))
    (implies
     (and (mathd362-real-p x)
          (mathd362-real-p y))
     (equal (mathd362-mul x y)
            (mathd362-mul y x)))
    (implies
     (mathd362-real-p x)
     (equal (mathd362-mul x (mathd362-one)) x))
    (implies
     (and
      (mathd362-real-p x)
      (not (equal x (mathd362-zero))))
     (equal
      (mathd362-mul x (mathd362-inv x))
      (mathd362-one)))
    (equal (mathd362-inv (mathd362-zero))
           (mathd362-zero))
    (implies
     (and
      (mathd362-real-p x)
      (mathd362-real-p y)
      (mathd362-real-p z))
     (equal
      (mathd362-mul x (mathd362-add y z))
      (mathd362-add
       (mathd362-mul x y)
       (mathd362-mul x z)))))))

(defun-sk mathd362-order-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (mathd362-real-p x)
     (not (mathd362-lt x x)))
    (implies
     (and (mathd362-real-p x)
          (mathd362-real-p y))
     (or (mathd362-lt x y)
         (equal x y)
         (mathd362-lt y x)))
    (implies
     (and
      (mathd362-real-p x)
      (mathd362-real-p y)
      (mathd362-real-p z)
      (mathd362-lt x y)
      (mathd362-lt y z))
     (mathd362-lt x z))
    (implies
     (and
      (mathd362-real-p x)
      (mathd362-real-p y)
      (mathd362-real-p z))
     (iff
      (mathd362-lt x y)
      (mathd362-lt
       (mathd362-add x z)
       (mathd362-add y z))))
    (implies
     (and
      (mathd362-real-p x)
      (mathd362-real-p y)
      (mathd362-lt (mathd362-zero) x)
      (mathd362-lt (mathd362-zero) y))
     (mathd362-lt
      (mathd362-zero)
      (mathd362-mul x y))))))

(defun-sk mathd362-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd362-real-p (mathd362-of-rational p))
     (equal (mathd362-of-rational 0)
            (mathd362-zero))
     (equal (mathd362-of-rational 1)
            (mathd362-one))
     (equal
      (mathd362-of-rational (+ p q))
      (mathd362-add
       (mathd362-of-rational p)
       (mathd362-of-rational q)))
     (equal
      (mathd362-of-rational (* p q))
      (mathd362-mul
       (mathd362-of-rational p)
       (mathd362-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd362-of-rational p)
       (mathd362-of-rational q)))
     (iff
      (< p q)
      (mathd362-lt
       (mathd362-of-rational p)
       (mathd362-of-rational q)))))))

(defun-sk mathd362-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd362-lt x (mathd362-natural n)))))

(defun-sk mathd362-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd362-real-p x)
    (mathd362-natural-bound-exists-p x))))

(defun mathd362-real-field-p ()
  (and
   (mathd362-real-p (mathd362-zero))
   (mathd362-real-p (mathd362-one))
   (not (equal (mathd362-zero) (mathd362-one)))
   (mathd362-lt (mathd362-zero) (mathd362-one))
   (mathd362-field-laws-p)
   (mathd362-order-laws-p)
   (mathd362-rational-laws-p)
   (mathd362-archimedean-p)))

(defun-sk mathd-algebra-362-statement-p ()
  (forall
   (a b)
   (implies
    (and
     (mathd362-real-field-p)
     (mathd362-real-p a)
     (mathd362-real-p b)
     (equal
      (mathd362-mul
       (mathd362-pow a 2)
       (mathd362-pow b 3))
      (mathd362-of-rational 32/27))
     (equal
      (mathd362-div a (mathd362-pow b 3))
      (mathd362-of-rational 27/4)))
    (equal
     (mathd362-add a b)
     (mathd362-of-rational 8/3)))))

(value-triple :itpeval-statement-checked)
:q
