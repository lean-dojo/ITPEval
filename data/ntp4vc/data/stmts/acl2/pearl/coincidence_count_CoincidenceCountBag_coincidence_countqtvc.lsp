;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/coincidence_count_CoincidenceCountBag_coincidence_countqtvc: the
;; coincidence-count loop invariant for two increasing integer lists, using
;; multiset intersections of list suffixes. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integer
;; values and lists. Int.toNat sends negative integers to zero, and List.get!
;; returns the integer default zero outside the list.

(defun ntp4vc-cc-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-cc-integer-list-p (cdr xs)))))

(defun ntp4vc-cc-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-cc-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-cc-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; The source multisets arise from finite list slices. Lists modulo element
;; multiplicity are an exact representation here; intersection removes one
;; matching occurrence from the right multiset for each retained occurrence.

(defun ntp4vc-cc-remove-first (value xs)
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (ntp4vc-cc-remove-first value (cdr xs))))))

(defun ntp4vc-cc-multiset-intersection (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      nil
    (if (member-equal (car left) right)
        (cons
         (car left)
         (ntp4vc-cc-multiset-intersection
          (cdr left)
          (ntp4vc-cc-remove-first (car left) right)))
      (ntp4vc-cc-multiset-intersection
       (cdr left)
       right))))

(defun ntp4vc-cc-overlap-card (left right)
  (len (ntp4vc-cc-multiset-intersection left right)))

(defun ntp4vc-cc-list-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      xs
    (ntp4vc-cc-list-drop (- count 1) (cdr xs))))

(defun ntp4vc-cc-list-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      nil
    (cons
     (car xs)
     (ntp4vc-cc-list-take (- count 1) (cdr xs)))))

;; On the source-specified domain 0 <= lo <= hi <= length(a), this slice is
;; definitionally the unique multiset satisfying bagofsub's recursion.

(defun ntp4vc-cc-bagofsub (a lo hi)
  (ntp4vc-cc-list-take
   (nfix (- hi lo))
   (ntp4vc-cc-list-drop (ntp4vc-cc-int-to-nat lo) a)))

(defun ntp4vc-cc-bagof (a)
  (ntp4vc-cc-bagofsub a 0 (len a)))

(defun ntp4vc-cc-drop (a index)
  (ntp4vc-cc-bagofsub a index (len a)))

;; Preserve the source's universal quantification over mathematical integer
;; indices in the definition of increasing.

(defun-sk ntp4vc-cc-increasing-p (a)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len a)))
     (<=
      (ntp4vc-cc-nth-int i a)
      (ntp4vc-cc-nth-int j a)))))

(defun ntp4vc-cc-full-overlap-card (a b)
  (ntp4vc-cc-overlap-card
   (ntp4vc-cc-bagof a)
   (ntp4vc-cc-bagof b)))

(defun ntp4vc-cc-suffix-overlap-card (a b i j)
  (ntp4vc-cc-overlap-card
   (ntp4vc-cc-drop a i)
   (ntp4vc-cc-drop b j)))

;; This is the exact conditional loop-step conclusion for fixed c, j, i, and
;; the source Boolean o1.

(defun ntp4vc-cc-loop-step-p (a b c j i o1)
  (implies
   (equal
    o1
    (if (< i (len a))
        (if (< j (len b)) t nil)
      nil))
   (if (equal o1 t)
       (and
        (<= 0 j)
        (< j (len b))
        (<= 0 i)
        (< i (len a))
        (if (< (ntp4vc-cc-nth-int i a)
               (ntp4vc-cc-nth-int j b))
            (and
             (<= 0 (+ (- (len a) i)
                      (- (len b) j)))
             (< (+ (- (len a) (+ i 1))
                   (- (len b) j))
                (+ (- (len a) i)
                   (- (len b) j)))
             (<= 0 (+ i 1))
             (<= (+ i 1) (len a))
             (<= 0 j)
             (<= j (len b))
             (equal
              (+ c
                 (ntp4vc-cc-suffix-overlap-card
                  a b (+ i 1) j))
              (ntp4vc-cc-full-overlap-card a b)))
          (and
           (<= 0 j)
           (< j (len b))
           (<= 0 i)
           (< i (len a))
           (if (< (ntp4vc-cc-nth-int j b)
                  (ntp4vc-cc-nth-int i a))
               (and
                (<= 0 (+ (- (len a) i)
                         (- (len b) j)))
                (< (+ (- (len a) i)
                      (- (len b) (+ j 1)))
                   (+ (- (len a) i)
                      (- (len b) j)))
                (<= 0 i)
                (<= i (len a))
                (<= 0 (+ j 1))
                (<= (+ j 1) (len b))
                (equal
                 (+ c
                    (ntp4vc-cc-suffix-overlap-card
                     a b i (+ j 1)))
                 (ntp4vc-cc-full-overlap-card a b)))
             (and
              (<= 0 (+ (- (len a) i)
                       (- (len b) j)))
              (< (+ (- (len a) (+ i 1))
                    (- (len b) (+ j 1)))
                 (+ (- (len a) i)
                    (- (len b) j)))
              (<= 0 (+ i 1))
              (<= (+ i 1) (len a))
              (<= 0 (+ j 1))
              (<= (+ j 1) (len b))
              (equal
               (+ c
                  1
                  (ntp4vc-cc-suffix-overlap-card
                   a b (+ i 1) (+ j 1)))
               (ntp4vc-cc-full-overlap-card a b)))))))
     (equal c (ntp4vc-cc-full-overlap-card a b)))))

;; Bool is represented by the exact two-element ACL2 Boolean domain.

(defun-sk ntp4vc-cc-all-booleans-step-p (a b c j i)
  (forall (o1)
    (implies
     (booleanp o1)
     (ntp4vc-cc-loop-step-p a b c j i o1))))

(defun-sk ntp4vc-cc-loop-vc-p (a b)
  (forall (c j i)
    (implies
     (and
      (integerp c)
      (integerp j)
      (integerp i))
     (implies
      (and
       (<= 0 i)
       (<= i (len a))
       (<= 0 j)
       (<= j (len b))
       (equal
        (+ c (ntp4vc-cc-suffix-overlap-card a b i j))
        (ntp4vc-cc-full-overlap-card a b)))
      (ntp4vc-cc-all-booleans-step-p a b c j i)))))

(defun
  ntp4vc-pearl-coincidence-count-coincidencecountbag-coincidence-countqtvc-statement
  (a b)
  (implies
   (and
    (ntp4vc-cc-integer-list-p a)
    (ntp4vc-cc-integer-list-p b)
    (ntp4vc-cc-increasing-p a)
    (ntp4vc-cc-increasing-p b))
   (and
    (<= 0 0)
    (<= 0 (len a))
    (<= 0 0)
    (<= 0 (len b))
    (equal
     (+ 0 (ntp4vc-cc-suffix-overlap-card a b 0 0))
     (ntp4vc-cc-full-overlap-card a b))
    (ntp4vc-cc-loop-vc-p a b))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
