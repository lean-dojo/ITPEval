;; Statement-only formalization of Hundred Theorems artifact 046, "The
;; Solution of the General Quartic Equation": Ferrari's formulas characterize
;; the roots of a quartic over an arbitrary field of characteristic not two.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative generic function symbols are ACL2's standard mechanism
;; for stating a theorem uniformly over an arbitrary algebraic structure.
(defstub ht046-carrier (x) t)
(defstub ht046-add-op (x y) t)
(defstub ht046-multiply-op (x y) t)
(defstub ht046-negate-op (x) t)
(defstub ht046-inverse-op (x) t)

(defun ht046-member-p (x)
  (if (ht046-carrier x) t nil))

(defun ht046-add (x y)
  (ht046-add-op x y))

(defun ht046-mul (x y)
  (ht046-multiply-op x y))

(defun ht046-neg (x)
  (ht046-negate-op x))

(defun ht046-inv (x)
  (ht046-inverse-op x))

(defun ht046-sub (x y)
  (ht046-add x (ht046-neg y)))

(defun ht046-div (x y)
  (ht046-mul x (ht046-inv y)))

(defun ht046-mul3 (x y z)
  (ht046-mul (ht046-mul x y) z))

(defun ht046-mul4 (x y z w)
  (ht046-mul (ht046-mul3 x y z) w))

(defun ht046-all-members-p (objects)
  (if (consp objects)
      (and
       (ht046-member-p (car objects))
       (ht046-all-members-p (cdr objects)))
    (equal objects nil)))

(defun-sk ht046-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht046-member-p x)
      (ht046-member-p y)
      (ht046-member-p z))
     (and
      (ht046-member-p (ht046-add x y))
      (ht046-member-p (ht046-mul x y))
      (ht046-member-p (ht046-neg x))
      (ht046-member-p (ht046-inv x))
      (equal (ht046-add (ht046-add x y) z)
             (ht046-add x (ht046-add y z)))
      (equal (ht046-add x y) (ht046-add y x))
      (equal (ht046-add x zero) x)
      (equal (ht046-add x (ht046-neg x)) zero)
      (equal (ht046-mul (ht046-mul x y) z)
             (ht046-mul x (ht046-mul y z)))
      (equal (ht046-mul x y) (ht046-mul y x))
      (equal (ht046-mul x one) x)
      (equal (ht046-inv zero) zero)
      (implies
       (not (equal x zero))
       (equal (ht046-mul x (ht046-inv x)) one))
      (equal (ht046-mul x (ht046-add y z))
             (ht046-add (ht046-mul x y)
                        (ht046-mul x z)))))))

(defun ht046-field-p (zero one)
  (and
   (ht046-member-p zero)
   (ht046-member-p one)
   (not (equal zero one))
   (ht046-field-laws-p zero one)))

(defun ht046-natural-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ht046-add one
               (ht046-natural-value (- n 1) zero one))))

(defun ht046-power (x exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (ht046-mul x (ht046-power x (- exponent 1) one))))

(defun ht046-ferrari-p (a b c zero one)
  (let* ((three (ht046-natural-value 3 zero one))
         (eight (ht046-natural-value 8 zero one))
         (a2 (ht046-power a 2 one))
         (b2 (ht046-power b 2 one))
         (numerator
          (ht046-sub
           (ht046-mul3 eight a c)
           (ht046-mul three b2)))
         (denominator (ht046-mul eight a2)))
    (ht046-div numerator denominator)))

(defun ht046-ferrari-q (a b c d zero one)
  (let* ((four (ht046-natural-value 4 zero one))
         (eight (ht046-natural-value 8 zero one))
         (a2 (ht046-power a 2 one))
         (a3 (ht046-power a 3 one))
         (b3 (ht046-power b 3 one))
         (numerator
          (ht046-add
           (ht046-sub b3 (ht046-mul4 four a b c))
           (ht046-mul3 eight a2 d)))
         (denominator (ht046-mul eight a3)))
    (ht046-div numerator denominator)))

(defun ht046-ferrari-r (a b c d e zero one)
  (let* ((three (ht046-natural-value 3 zero one))
         (sixteen (ht046-natural-value 16 zero one))
         (sixty-four (ht046-natural-value 64 zero one))
         (two-hundred-fifty-six (ht046-natural-value 256 zero one))
         (a2 (ht046-power a 2 one))
         (a3 (ht046-power a 3 one))
         (a4 (ht046-power a 4 one))
         (b2 (ht046-power b 2 one))
         (b4 (ht046-power b 4 one))
         (positive-part
          (ht046-add
           (ht046-mul4 sixteen a b2 c)
           (ht046-mul3 two-hundred-fifty-six a3 e)))
         (numerator
          (ht046-sub
           (ht046-sub positive-part (ht046-mul three b4))
           (ht046-mul4 sixty-four a2 b d)))
         (denominator (ht046-mul two-hundred-fifty-six a4)))
    (ht046-div numerator denominator)))

(defun ht046-quartic-value (a b c d e x one)
  (ht046-add
   (ht046-add
    (ht046-add
     (ht046-add
      (ht046-mul a (ht046-power x 4 one))
      (ht046-mul b (ht046-power x 3 one)))
     (ht046-mul c (ht046-power x 2 one)))
    (ht046-mul d x))
   e))

(defun ht046-ferrari-base-p
    (zero one a b c d e p q r v w x)
  (let ((two (ht046-natural-value 2 zero one)))
    (and
     (ht046-field-p zero one)
     (ht046-all-members-p (list a b c d e p q r v w x))
     (not (equal two zero))
     (not (equal a zero))
     (equal p (ht046-ferrari-p a b c zero one))
     (equal q (ht046-ferrari-q a b c d zero one))
     (equal r (ht046-ferrari-r a b c d e zero one)))))

(defun ht046-ferrari-radical-data-p
    (zero one p q r u s tau v w)
  (let* ((two (ht046-natural-value 2 zero one))
         (four (ht046-natural-value 4 zero one))
         (eight (ht046-natural-value 8 zero one))
         (p2 (ht046-power p 2 one))
         (q2 (ht046-power q 2 one))
         (u2 (ht046-power u 2 one))
         (u3 (ht046-power u 3 one))
         (s2 (ht046-power s 2 one))
         (tau2 (ht046-power tau 2 one))
         (v2 (ht046-power v 2 one))
         (w2 (ht046-power w 2 one)))
    (if (equal q zero)
        (and
         (ht046-member-p tau)
         (equal tau2 (ht046-sub p2 (ht046-mul four r)))
         (equal v2
                (ht046-div
                 (ht046-add (ht046-neg p) tau)
                 two))
         (equal w2
                (ht046-div
                 (ht046-sub (ht046-neg p) tau)
                 two)))
      (let* ((resolvent
              (ht046-sub
               (ht046-add
                (ht046-sub
                 (ht046-sub u3 (ht046-mul p u2))
                 (ht046-mul3 four r u))
                (ht046-mul3 four p r))
               q2))
             (q-over-s (ht046-div q s))
             (four-s2 (ht046-mul four s2)))
        (and
         (ht046-all-members-p (list u s))
         (equal resolvent zero)
         (equal s2 (ht046-sub u p))
         (equal v2
                (ht046-sub
                 four-s2
                 (ht046-mul eight (ht046-sub u q-over-s))))
         (equal w2
                (ht046-sub
                 four-s2
                 (ht046-mul eight (ht046-add u q-over-s)))))))))

(defun ht046-ferrari-root-characterization-p
    (zero one a b c d e q s v w x)
  (let* ((two (ht046-natural-value 2 zero one))
         (four (ht046-natural-value 4 zero one))
         (shift (ht046-div b (ht046-mul four a)))
         (two-s (ht046-mul two s))
         (minus-two-s (ht046-neg two-s))
         (root-one
          (if (equal q zero)
              (ht046-sub v shift)
            (ht046-sub
             (ht046-div (ht046-sub minus-two-s v) four)
             shift)))
         (root-two
          (if (equal q zero)
              (ht046-sub (ht046-neg v) shift)
            (ht046-sub
             (ht046-div (ht046-add minus-two-s v) four)
             shift)))
         (root-three
          (if (equal q zero)
              (ht046-sub w shift)
            (ht046-sub
             (ht046-div (ht046-sub two-s w) four)
             shift)))
         (root-four
          (if (equal q zero)
              (ht046-sub (ht046-neg w) shift)
            (ht046-sub
             (ht046-div (ht046-add two-s w) four)
             shift))))
    (equal
     (equal (ht046-quartic-value a b c d e x one) zero)
     (or
      (equal x root-one)
      (equal x root-two)
      (equal x root-three)
      (equal x root-four)))))

(defun hundred-theorems-046-solution-of-general-quartic-statement
    (zero one a b c d e p q r u s tau v w x)
  (implies
   (and
    (ht046-ferrari-base-p
     zero one a b c d e p q r v w x)
    (ht046-ferrari-radical-data-p
     zero one p q r u s tau v w))
   (ht046-ferrari-root-characterization-p
    zero one a b c d e q s v w x)))

(value-triple :itpeval-statement-checked)
:q
