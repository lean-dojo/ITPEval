;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/coincidence_count_CoincidenceCount_coincidence_countqtvc: the
;; coincidence-count loop invariant for two strictly increasing integer lists,
;; using finite-set intersections of list suffixes. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integer
;; values and lists. Int.toNat sends negative integers to zero, and List.get!
;; returns the integer default zero outside the list.

(defun ntp4vc-ccset-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-ccset-integer-list-p (cdr xs)))))

(defun ntp4vc-ccset-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-ccset-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-ccset-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; A duplicate-free list represents a finite set extensionally. Setification
;; is exactly the image of the relevant source index interval under list
;; lookup; order is immaterial, and membership/cardinality are preserved.

(defun ntp4vc-ccset-setify (xs)
  (if (endp xs)
      nil
    (let ((tail-set
           (ntp4vc-ccset-setify (cdr xs))))
      (if (member-equal (car xs) tail-set)
          tail-set
        (cons (car xs) tail-set)))))

(defun ntp4vc-ccset-intersection-card (left-set right-set)
  (if (endp left-set)
      0
    (+
     (if (member-equal (car left-set) right-set)
         1
       0)
     (ntp4vc-ccset-intersection-card
      (cdr left-set)
      right-set))))

(defun ntp4vc-ccset-overlap-card (left right)
  (ntp4vc-ccset-intersection-card
   (ntp4vc-ccset-setify left)
   (ntp4vc-ccset-setify right)))

(defun ntp4vc-ccset-list-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      xs
    (ntp4vc-ccset-list-drop (- count 1) (cdr xs))))

(defun ntp4vc-ccset-drop (a index)
  (ntp4vc-ccset-list-drop
   (ntp4vc-ccset-int-to-nat index)
   a))

;; Preserve the source's universal quantification over mathematical integer
;; indices and its strict increasingness condition.

(defun-sk ntp4vc-ccset-increasing-p (a)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len a)))
     (<
      (ntp4vc-ccset-nth-int i a)
      (ntp4vc-ccset-nth-int j a)))))

(defun ntp4vc-ccset-full-overlap-card (a b)
  (ntp4vc-ccset-overlap-card a b))

(defun ntp4vc-ccset-suffix-overlap-card (a b i j)
  (ntp4vc-ccset-overlap-card
   (ntp4vc-ccset-drop a i)
   (ntp4vc-ccset-drop b j)))

;; This is the exact conditional loop-step conclusion for fixed c, j, i, and
;; the source Boolean o1.

(defun ntp4vc-ccset-loop-step-p (a b c j i o1)
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
        (if (< (ntp4vc-ccset-nth-int i a)
               (ntp4vc-ccset-nth-int j b))
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
                 (ntp4vc-ccset-suffix-overlap-card
                  a b (+ i 1) j))
              (ntp4vc-ccset-full-overlap-card a b)))
          (and
           (<= 0 j)
           (< j (len b))
           (<= 0 i)
           (< i (len a))
           (if (< (ntp4vc-ccset-nth-int j b)
                  (ntp4vc-ccset-nth-int i a))
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
                    (ntp4vc-ccset-suffix-overlap-card
                     a b i (+ j 1)))
                 (ntp4vc-ccset-full-overlap-card a b)))
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
                  (ntp4vc-ccset-suffix-overlap-card
                   a b (+ i 1) (+ j 1)))
               (ntp4vc-ccset-full-overlap-card a b)))))))
     (equal c (ntp4vc-ccset-full-overlap-card a b)))))

;; Bool is represented by the exact two-element ACL2 Boolean domain.

(defun-sk ntp4vc-ccset-all-booleans-step-p (a b c j i)
  (forall (o1)
    (implies
     (booleanp o1)
     (ntp4vc-ccset-loop-step-p a b c j i o1))))

(defun-sk ntp4vc-ccset-loop-vc-p (a b)
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
        (+ c (ntp4vc-ccset-suffix-overlap-card a b i j))
        (ntp4vc-ccset-full-overlap-card a b)))
      (ntp4vc-ccset-all-booleans-step-p a b c j i)))))

(defun
  ntp4vc-pearl-coincidence-count-coincidencecount-coincidence-countqtvc-statement
  (a b)
  (implies
   (and
    (ntp4vc-ccset-integer-list-p a)
    (ntp4vc-ccset-integer-list-p b)
    (ntp4vc-ccset-increasing-p a)
    (ntp4vc-ccset-increasing-p b))
   (and
    (<= 0 0)
    (<= 0 (len a))
    (<= 0 0)
    (<= 0 (len b))
    (equal
     (+ 0 (ntp4vc-ccset-suffix-overlap-card a b 0 0))
     (ntp4vc-ccset-full-overlap-card a b))
    (ntp4vc-ccset-loop-vc-p a b))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
