;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/algo64_Algo64_quicksortqtvc: the quicksort verification condition
;; composing a partition with recursively sorted subranges of an integer list.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's integers and finite true lists directly represent the source integer
;; lists.  The conversion below is Int.toNat, including its value zero on
;; negative integers.

(defun ntp4vc-qsort-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and (integerp (car xs))
         (ntp4vc-qsort-integer-list-p (cdr xs)))))

(defun ntp4vc-qsort-int-to-nat (z)
  (if (and (integerp z) (< z 0))
      0
    (nfix z)))

(defun ntp4vc-qsort-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      xs
    (ntp4vc-qsort-drop (- count 1) (cdr xs))))

(defun ntp4vc-qsort-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      nil
    (cons (car xs)
          (ntp4vc-qsort-take (- count 1) (cdr xs)))))

(defun ntp4vc-qsort-slice (xs lower upper)
  (ntp4vc-qsort-take
   (- (nfix upper) (nfix lower))
   (ntp4vc-qsort-drop (nfix lower) xs)))

(defun ntp4vc-qsort-remove-first (value xs)
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons (car xs)
            (ntp4vc-qsort-remove-first value (cdr xs))))))

(defun ntp4vc-qsort-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and (member-equal (car left) right)
         (ntp4vc-qsort-permutation-p
          (cdr left)
          (ntp4vc-qsort-remove-first (car left) right)))))

;; This is List.permut_sub': equal total lengths and unchanged prefix and
;; suffix, with a permutation of the half-open slice [lower, upper).

(defun ntp4vc-qsort-permut-sub-prime-p
    (left right lower upper)
  (and
   (equal (len left) (len right))
   (equal
    (ntp4vc-qsort-slice left 0 lower)
    (ntp4vc-qsort-slice right 0 lower))
   (equal
    (ntp4vc-qsort-slice left upper (len left))
    (ntp4vc-qsort-slice right upper (len right)))
   (ntp4vc-qsort-permutation-p
    (ntp4vc-qsort-slice left lower upper)
    (ntp4vc-qsort-slice right lower upper))))

(defun ntp4vc-qsort-nth-int (index xs)
  (let ((value (nth (ntp4vc-qsort-int-to-nat index) xs)))
    (if (integerp value) value 0)))

;; sorted_sub1 quantifies over all integer indices in the half-open range.

(defun-sk ntp4vc-qsort-sorted-sub1-p (xs lower upper)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2)
      (<= lower i1)
      (<= i1 i2)
      (< i2 upper))
     (<= (ntp4vc-qsort-nth-int i1 xs)
         (ntp4vc-qsort-nth-int i2 xs)))))

(defun-sk ntp4vc-qsort-left-band-p (xs lower upper pivot)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= lower k)
      (<= k upper))
     (<= (ntp4vc-qsort-nth-int k xs) pivot))))

(defun-sk ntp4vc-qsort-middle-band-p (xs lower upper pivot)
  (forall (k)
    (implies
     (and
      (integerp k)
      (< lower k)
      (< k upper))
     (equal (ntp4vc-qsort-nth-int k xs) pivot))))

(defun-sk ntp4vc-qsort-right-band-p (xs lower upper pivot)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= lower k)
      (<= k upper))
     (<= pivot (ntp4vc-qsort-nth-int k xs)))))

(defun ntp4vc-qsort-partition-p
    (t1 t2 m n i j pivot)
  (and
   (ntp4vc-qsort-permut-sub-prime-p
    t1 t2
    (ntp4vc-qsort-int-to-nat m)
    (ntp4vc-qsort-int-to-nat (+ n 1)))
   (ntp4vc-qsort-left-band-p t2 m j pivot)
   (ntp4vc-qsort-middle-band-p t2 j i pivot)
   (ntp4vc-qsort-right-band-p t2 i n pivot)))

;; The following three predicates retain the source's nested universal
;; continuations for the first partition result and the two recursive calls.

(defun-sk ntp4vc-qsort-after-right-recursion-p
    (m n original a2 i)
  (forall (a3)
    (implies
     (ntp4vc-qsort-integer-list-p a3)
     (implies
      (equal (len a3) (len a2))
      (implies
       (and
        (ntp4vc-qsort-permut-sub-prime-p
         a2 a3
         (ntp4vc-qsort-int-to-nat i)
         (ntp4vc-qsort-int-to-nat (+ n 1)))
        (ntp4vc-qsort-sorted-sub1-p a3 i (+ n 1)))
       (and
        (ntp4vc-qsort-permut-sub-prime-p
         original a3
         (ntp4vc-qsort-int-to-nat m)
         (ntp4vc-qsort-int-to-nat (+ n 1)))
        (ntp4vc-qsort-sorted-sub1-p a3 m (+ n 1))))))))

(defun-sk ntp4vc-qsort-after-left-recursion-p
    (m n original a1 i j)
  (forall (a2)
    (implies
     (ntp4vc-qsort-integer-list-p a2)
     (implies
      (equal (len a2) (len a1))
      (implies
       (and
        (ntp4vc-qsort-permut-sub-prime-p
         a1 a2
         (ntp4vc-qsort-int-to-nat m)
         (ntp4vc-qsort-int-to-nat (+ j 1)))
        (ntp4vc-qsort-sorted-sub1-p a2 m (+ j 1)))
       (and
        (and
         (<= 0 (- n m))
         (< (- n i) (- n m)))
        (and
         (<= 0 i)
         (<= i n)
         (< n (len a2)))
        (ntp4vc-qsort-after-right-recursion-p
         m n original a2 i)))))))

(defun-sk ntp4vc-qsort-partition-continuation-p
    (m n original)
  (forall (j i a1)
    (implies
     (and
      (integerp j)
      (integerp i)
      (ntp4vc-qsort-integer-list-p a1))
     (implies
      (equal (len a1) (len original))
      (implies
       (and
        (<= m j)
        (< j i)
        (<= i n)
        (ntp4vc-qsort-partition-p
         original a1 m n i j 42))
       (and
        (and
         (<= 0 (- n m))
         (< (- j m) (- n m)))
        (and
         (<= 0 m)
         (<= m j)
         (< j (len a1)))
        (ntp4vc-qsort-after-left-recursion-p
         m n original a1 i j)))))))

(defun ntp4vc-pearl-algo64-algo64-quicksortqtvc-statement
    (m n a)
  (implies
   (and
    (integerp m)
    (integerp n)
    (ntp4vc-qsort-integer-list-p a)
    (<= 0 m)
    (<= m n)
    (< n (len a)))
   (if (< m n)
       (and
        (<= 0 m)
        (< m n)
        (< n (len a))
        (ntp4vc-qsort-partition-continuation-p m n a))
     (and
      (ntp4vc-qsort-permut-sub-prime-p
       a a
       (ntp4vc-qsort-int-to-nat m)
       (ntp4vc-qsort-int-to-nat (+ n 1)))
      (ntp4vc-qsort-sorted-sub1-p a m (+ n 1))))))

(value-triple :itpeval-statement-checked)
:q
