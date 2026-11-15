;; Statement-only formalization of miniF2F artifact mathd_algebra_388:
;; for all real x, y, and z, the two source linear equations imply x=14.
;; This file contains no proof.
;;
;; ACL2 has no native real field. The explicit commutative ring
;; carrier below preserves all three source variables and both equations.
;; In particular, y and z are not narrowed to rationals. Every structural law
;; is a statement premise, and no premise assumes the solved value of x.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd388-real-p (value) t)
(defstub mathd388-zero () t)
(defstub mathd388-one () t)
(defstub mathd388-add (left right) t)
(defstub mathd388-mul (left right) t)
(defstub mathd388-neg (value) t)

(defun mathd388-sub (left right)
  (mathd388-add left (mathd388-neg right)))

(defun mathd388-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd388-zero)
    (mathd388-add
     (mathd388-one)
     (mathd388-natural (1- n)))))

(defun-sk mathd388-ring-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd388-real-p x)
          (mathd388-real-p y))
     (and
      (mathd388-real-p (mathd388-add x y))
      (mathd388-real-p (mathd388-mul x y))))
    (implies
     (mathd388-real-p x)
     (mathd388-real-p (mathd388-neg x)))
    (implies
     (and
      (mathd388-real-p x)
      (mathd388-real-p y)
      (mathd388-real-p z))
     (equal
      (mathd388-add (mathd388-add x y) z)
      (mathd388-add x (mathd388-add y z))))
    (implies
     (and (mathd388-real-p x)
          (mathd388-real-p y))
     (equal (mathd388-add x y)
            (mathd388-add y x)))
    (implies
     (mathd388-real-p x)
     (and
      (equal (mathd388-add x (mathd388-zero)) x)
      (equal
       (mathd388-add x (mathd388-neg x))
       (mathd388-zero))))
    (implies
     (and
      (mathd388-real-p x)
      (mathd388-real-p y)
      (mathd388-real-p z))
     (equal
      (mathd388-mul (mathd388-mul x y) z)
      (mathd388-mul x (mathd388-mul y z))))
    (implies
     (and (mathd388-real-p x)
          (mathd388-real-p y))
     (equal (mathd388-mul x y)
            (mathd388-mul y x)))
    (implies
     (mathd388-real-p x)
     (equal (mathd388-mul x (mathd388-one)) x))
    (implies
     (and
      (mathd388-real-p x)
      (mathd388-real-p y)
      (mathd388-real-p z))
     (equal
      (mathd388-mul x (mathd388-add y z))
      (mathd388-add
       (mathd388-mul x y)
       (mathd388-mul x z)))))))

(defun mathd388-commutative-ring-p ()
  (and
   (mathd388-real-p (mathd388-zero))
   (mathd388-real-p (mathd388-one))
   (not (equal (mathd388-zero)
               (mathd388-one)))
   (mathd388-ring-laws-p)))

(defun-sk mathd-algebra-388-statement-p ()
  (forall
   (x y z)
   (implies
    (and
     (mathd388-commutative-ring-p)
     (mathd388-real-p x)
     (mathd388-real-p y)
     (mathd388-real-p z)
     (equal
      (mathd388-sub
       (mathd388-add
        (mathd388-mul (mathd388-natural 3) x)
        (mathd388-mul (mathd388-natural 4) y))
       (mathd388-mul (mathd388-natural 12) z))
      (mathd388-natural 10))
     (equal
      (mathd388-add
       (mathd388-mul
        (mathd388-neg (mathd388-natural 2))
        x)
       (mathd388-add
        (mathd388-neg
         (mathd388-mul (mathd388-natural 3) y))
        (mathd388-mul (mathd388-natural 9) z)))
      (mathd388-neg (mathd388-natural 4))))
    (equal x (mathd388-natural 14)))))

(value-triple :itpeval-statement-checked)
:q
