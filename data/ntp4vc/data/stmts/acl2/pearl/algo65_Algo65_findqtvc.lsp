;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/algo65_Algo65_findqtvc: the find verification condition composing a
;; partition of an integer list with recursive subranges around index k.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integer
;; lists.  This conversion is Int.toNat, including zero for negative integers.

(defun ntp4vc-find-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-find-integer-list-p (cdr xs)))))

(defun ntp4vc-find-int-to-nat (z)
  (if (and (integerp z) (< z 0))
      0
    (nfix z)))

(defun ntp4vc-find-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      xs
    (ntp4vc-find-drop (- count 1) (cdr xs))))

(defun ntp4vc-find-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      nil
    (cons
     (car xs)
     (ntp4vc-find-take (- count 1) (cdr xs)))))

(defun ntp4vc-find-slice (xs lower upper)
  (ntp4vc-find-take
   (- (nfix upper) (nfix lower))
   (ntp4vc-find-drop (nfix lower) xs)))

(defun ntp4vc-find-remove-first (value xs)
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (ntp4vc-find-remove-first value (cdr xs))))))

(defun ntp4vc-find-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (ntp4vc-find-permutation-p
      (cdr left)
      (ntp4vc-find-remove-first (car left) right)))))

;; List.permut_sub' requires equal total lengths, equal prefix and suffix, and
;; a permutation of the half-open slice [lower, upper).

(defun ntp4vc-find-permut-sub-prime-p
    (left right lower upper)
  (and
   (equal (len left) (len right))
   (equal
    (ntp4vc-find-slice left 0 lower)
    (ntp4vc-find-slice right 0 lower))
   (equal
    (ntp4vc-find-slice left upper (len left))
    (ntp4vc-find-slice right upper (len right)))
   (ntp4vc-find-permutation-p
    (ntp4vc-find-slice left lower upper)
    (ntp4vc-find-slice right lower upper))))

;; List.get! on an integer list returns zero outside the list.

(defun ntp4vc-find-nth-int (index xs)
  (let ((value (nth (ntp4vc-find-int-to-nat index) xs)))
    (if (integerp value) value 0)))

(defun-sk ntp4vc-find-left-band-p
    (xs lower upper pivot)
  (forall (r)
    (implies
     (and
      (integerp r)
      (<= lower r)
      (<= r upper))
     (<= (ntp4vc-find-nth-int r xs) pivot))))

(defun-sk ntp4vc-find-middle-band-p
    (xs lower upper pivot)
  (forall (r)
    (implies
     (and
      (integerp r)
      (< lower r)
      (< r upper))
     (equal (ntp4vc-find-nth-int r xs) pivot))))

(defun-sk ntp4vc-find-right-band-p
    (xs lower upper pivot)
  (forall (r)
    (implies
     (and
      (integerp r)
      (<= lower r)
      (<= r upper))
     (<= pivot (ntp4vc-find-nth-int r xs)))))

(defun ntp4vc-find-partition-p
    (original result m n j i)
  (and
   (ntp4vc-find-permut-sub-prime-p
    original result
    (ntp4vc-find-int-to-nat m)
    (ntp4vc-find-int-to-nat (+ n 1)))
   (ntp4vc-find-left-band-p result m j 42)
   (ntp4vc-find-middle-band-p result j i 42)
   (ntp4vc-find-right-band-p result i n 42)))

;; A recursive subcall preserves the indicated slice and places the value at k
;; between every value to its left and every value to its right.

(defun ntp4vc-find-subcall-result-p
    (before after lower k upper)
  (and
   (ntp4vc-find-permut-sub-prime-p
    before after
    (ntp4vc-find-int-to-nat lower)
    (ntp4vc-find-int-to-nat (+ upper 1)))
   (ntp4vc-find-left-band-p
    after lower k (ntp4vc-find-nth-int k after))
   (ntp4vc-find-right-band-p
    after k upper (ntp4vc-find-nth-int k after))))

(defun-sk ntp4vc-find-after-right-subcall-p
    (m k n original before i)
  (forall (after)
    (implies
     (ntp4vc-find-integer-list-p after)
     (implies
      (equal (len after) (len before))
      (implies
       (ntp4vc-find-subcall-result-p before after i k n)
       (ntp4vc-find-subcall-result-p original after m k n))))))

(defun-sk ntp4vc-find-after-left-subcall-p
    (m k n original before i j)
  (forall (after)
    (implies
     (ntp4vc-find-integer-list-p after)
     (implies
      (equal (len after) (len before))
      (implies
       (ntp4vc-find-subcall-result-p before after m k j)
       (if (<= i k)
           (and
            (<= 0 (- n m))
            (< (- n i) (- n m))
            (<= 0 i)
            (<= i k)
            (<= k n)
            (< n (len after))
            (ntp4vc-find-after-right-subcall-p
             m k n original after i))
         (ntp4vc-find-subcall-result-p
          original after m k n)))))))

(defun-sk ntp4vc-find-partition-continuation-p
    (m k n original)
  (forall (j i partitioned)
    (implies
     (and
      (integerp j)
      (integerp i)
      (ntp4vc-find-integer-list-p partitioned))
     (implies
      (equal (len partitioned) (len original))
      (implies
       (and
        (<= m j)
        (< j i)
        (<= i n)
        (ntp4vc-find-partition-p
         original partitioned m n j i))
       (if (<= k j)
           (and
            (<= 0 (- n m))
            (< (- j m) (- n m))
            (<= 0 m)
            (<= m k)
            (<= k j)
            (< j (len partitioned))
            (ntp4vc-find-after-left-subcall-p
             m k n original partitioned i j))
         (if (<= i k)
             (and
              (<= 0 (- n m))
              (< (- n i) (- n m))
              (<= 0 i)
              (<= i k)
              (<= k n)
              (< n (len partitioned))
              (ntp4vc-find-after-right-subcall-p
               m k n original partitioned i))
           (ntp4vc-find-subcall-result-p
            original partitioned m k n))))))))

(defun ntp4vc-pearl-algo65-algo65-findqtvc-statement
    (m k n a)
  (implies
   (and
    (integerp m)
    (integerp k)
    (integerp n)
    (ntp4vc-find-integer-list-p a)
    (<= 0 m)
    (<= m k)
    (<= k n)
    (< n (len a)))
   (if (< m n)
       (and
        (<= 0 m)
        (< m n)
        (< n (len a))
        (ntp4vc-find-partition-continuation-p m k n a))
     (ntp4vc-find-subcall-result-p a a m k n))))

(value-triple :itpeval-statement-checked)
:q
