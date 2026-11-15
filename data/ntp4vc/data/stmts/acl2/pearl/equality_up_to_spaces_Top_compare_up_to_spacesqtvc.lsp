;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/equality_up_to_spaces_Top_compare_up_to_spacesqtvc: the complete
;; verification condition for comparing two character lists after recursively
;; removing space characters. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's full object universe represents the opaque source character type,
;; and finite true lists represent source character lists.  The source Boolean
;; equality test is uniquely fixed by eq'spec, so it is definitionally native
;; equality here.

(defun ntp4vc-eus-char-eq (left right)
  (if (equal left right) t nil))

;; This recursion is exactly remove_spaces'def on finite lists: the empty list
;; is unchanged, a leading space is discarded, and every other head is kept.

(defun ntp4vc-eus-remove-spaces (xs space)
  (if (endp xs)
      xs
    (if (equal
         (ntp4vc-eus-char-eq (car xs) space)
         t)
        (ntp4vc-eus-remove-spaces (cdr xs) space)
      (cons
       (car xs)
       (ntp4vc-eus-remove-spaces (cdr xs) space)))))

;; Int.toNat maps negative mathematical integers to zero.  All calls below
;; arise under the source integer domains.

(defun ntp4vc-eus-int-to-nat (value)
  (if (and (integerp value)
           (<= 0 value))
      value
    0))

(defun ntp4vc-eus-drop (index xs)
  (nthcdr (ntp4vc-eus-int-to-nat index) xs))

(defun ntp4vc-eus-nth (index xs)
  (nth (ntp4vc-eus-int-to-nat index) xs))

(defun ntp4vc-eus-full-equal-p (x y space)
  (equal
   (ntp4vc-eus-remove-spaces x space)
   (ntp4vc-eus-remove-spaces y space)))

(defun ntp4vc-eus-suffix-equal-p (x y space i j)
  (equal
   (ntp4vc-eus-remove-spaces
    (ntp4vc-eus-drop i x)
    space)
   (ntp4vc-eus-remove-spaces
    (ntp4vc-eus-drop j y)
    space)))

;; The innermost comparison branch retains the source quantification over o4,
;; its exact Boolean defining constraint, the equality-test specification, and
;; the three possible loop outcomes.

(defun ntp4vc-eus-both-advance-p (x y space i j n m)
  (and
   (<= 0 (+ (- n i) (- m j)))
   (<
    (+ (- n (+ i 1))
       (- m (+ j 1)))
    (+ (- n i) (- m j)))
   (<= 0 (+ i 1))
   (<= (+ i 1) n)
   (<= 0 (+ j 1))
   (<= (+ j 1) m)
   (iff
    (ntp4vc-eus-full-equal-p x y space)
    (ntp4vc-eus-suffix-equal-p
     x y space (+ i 1) (+ j 1)))))

(defun ntp4vc-eus-o4-body-p (x y space i j n m o4)
  (implies
   (equal
    o4
    (if (equal i n)
        t
      (if (equal j m) t nil)))
   (if (equal o4 t)
       (not (ntp4vc-eus-full-equal-p x y space))
     (let*
         ((o5 (ntp4vc-eus-nth j y))
          (o6 (ntp4vc-eus-nth i x))
          (o7 (ntp4vc-eus-char-eq o6 o5)))
       (implies
        (iff
         (equal o7 t)
         (equal o6 o5))
        (if (not (equal o7 t))
            (not (ntp4vc-eus-full-equal-p x y space))
          (ntp4vc-eus-both-advance-p
           x y space i j n m)))))))

(defun-sk ntp4vc-eus-all-o4-p (x y space i j n m)
  (forall (o4)
    (implies
     (booleanp o4)
     (ntp4vc-eus-o4-body-p x y space i j n m o4))))

;; The y-space branch keeps o3 universally quantified over the exact Boolean
;; domain and advances only j when the current y character is a space.

(defun ntp4vc-eus-y-advance-p (x y space i j n m)
  (and
   (<= 0 (+ (- n i) (- m j)))
   (<
    (+ (- n i)
       (- m (+ j 1)))
    (+ (- n i) (- m j)))
   (<= 0 i)
   (<= i n)
   (<= 0 (+ j 1))
   (<= (+ j 1) m)
   (iff
    (ntp4vc-eus-full-equal-p x y space)
    (ntp4vc-eus-suffix-equal-p
     x y space i (+ j 1)))))

(defun ntp4vc-eus-o3-constraint-p (y space j m o3)
  (if (< j m)
      (let*
          ((o4 space)
           (o5 (ntp4vc-eus-nth j y)))
        (and
         (equal o3 (ntp4vc-eus-char-eq o5 o4))
         (iff
          (equal o3 t)
          (equal o5 o4))))
    (equal o3 nil)))

(defun ntp4vc-eus-o3-body-p (x y space i j n m o3)
  (implies
   (ntp4vc-eus-o3-constraint-p y space j m o3)
   (if (equal o3 t)
       (ntp4vc-eus-y-advance-p x y space i j n m)
     (ntp4vc-eus-all-o4-p x y space i j n m))))

(defun-sk ntp4vc-eus-all-o3-p (x y space i j n m)
  (forall (o3)
    (implies
     (booleanp o3)
     (ntp4vc-eus-o3-body-p x y space i j n m o3))))

;; The x-space branch analogously retains o2 and advances only i.

(defun ntp4vc-eus-x-advance-p (x y space i j n m)
  (and
   (<= 0 (+ (- n i) (- m j)))
   (<
    (+ (- n (+ i 1))
       (- m j))
    (+ (- n i) (- m j)))
   (<= 0 (+ i 1))
   (<= (+ i 1) n)
   (<= 0 j)
   (<= j m)
   (iff
    (ntp4vc-eus-full-equal-p x y space)
    (ntp4vc-eus-suffix-equal-p
     x y space (+ i 1) j))))

(defun ntp4vc-eus-o2-constraint-p (x space i n o2)
  (if (< i n)
      (let*
          ((o3 space)
           (o4 (ntp4vc-eus-nth i x)))
        (and
         (equal o2 (ntp4vc-eus-char-eq o4 o3))
         (iff
          (equal o2 t)
          (equal o4 o3))))
    (equal o2 nil)))

(defun ntp4vc-eus-o2-body-p (x y space i j n m o2)
  (implies
   (ntp4vc-eus-o2-constraint-p x space i n o2)
   (if (equal o2 t)
       (ntp4vc-eus-x-advance-p x y space i j n m)
     (ntp4vc-eus-all-o3-p x y space i j n m))))

(defun-sk ntp4vc-eus-all-o2-p (x y space i j n m)
  (forall (o2)
    (implies
     (booleanp o2)
     (ntp4vc-eus-o2-body-p x y space i j n m o2))))

;; o1 records whether either list still has an unprocessed character.

(defun ntp4vc-eus-o1-body-p (x y space i j n m o1)
  (implies
   (equal
    o1
    (if (< i n)
        t
      (if (< j m) t nil)))
   (if (equal o1 t)
       (ntp4vc-eus-all-o2-p x y space i j n m)
     (ntp4vc-eus-full-equal-p x y space))))

(defun-sk ntp4vc-eus-all-o1-p (x y space i j n m)
  (forall (o1)
    (implies
     (booleanp o1)
     (ntp4vc-eus-o1-body-p x y space i j n m o1))))

;; Preserve the source universal order and domains for j and i, together with
;; the complete invariant hypothesis and nested Boolean branch obligations.

(defun-sk ntp4vc-eus-loop-vc-p (x y space n m)
  (forall (j i)
    (implies
     (and
      (integerp j)
      (integerp i))
     (implies
      (and
       (<= 0 i)
       (<= i n)
       (<= 0 j)
       (<= j m)
       (iff
        (ntp4vc-eus-full-equal-p x y space)
        (ntp4vc-eus-suffix-equal-p x y space i j)))
      (ntp4vc-eus-all-o1-p x y space i j n m)))))

(defun ntp4vc-eus-vc-body-p (x y space)
  (let*
      ((n (len x))
       (m (len y)))
    (and
     (<= 0 0)
     (<= 0 n)
     (<= 0 0)
     (<= 0 m)
     (iff
      (ntp4vc-eus-full-equal-p x y space)
      (ntp4vc-eus-suffix-equal-p x y space 0 0))
     (ntp4vc-eus-loop-vc-p x y space n m))))

(defun-sk
    ntp4vc-pearl-equality-up-to-spaces-top-compare-up-to-spacesqtvc-statement
    ()
  (forall (x y space)
    (implies
     (and
      (true-listp x)
      (true-listp y))
     (ntp4vc-eus-vc-body-p x y space))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
