;; Statement-only formalization of NTP4VC artifact
;; pearl/verifythis_2024_challenge1_Top_smart_array_copy_0bqtvc: the
;; verification condition for smart array copying by shuffled subsegments,
;; including permutation-pair, chunk-copy, loop-invariant, and frame
;; conditions. This file contains no proof.

(in-package "ACL2")

;; Why3 integer-to-natural coercion, used for logical array indices.
(defun sac0b-z-to-nat (z)
  (if (and (integerp z)
           (< 0 z))
      z
    0))

(defun sac0b-integer-listp (values)
  (if (consp values)
      (and (integerp (car values))
           (sac0b-integer-listp (cdr values)))
    (equal values nil)))

(defun-sk sac0b-permutation-range-p (l p)
  (forall i
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i l))
     (let ((p-at-i (nth (sac0b-z-to-nat i) p)))
       (and (integerp p-at-i)
            (<= 0 p-at-i)
            (< p-at-i l))))))

(defun-sk sac0b-permutation-distinct-p (l p)
  (forall (i j)
    (implies
     (and (integerp i)
          (integerp j)
          (<= 0 i)
          (< i l)
          (<= 0 j)
          (< j l)
          (not (equal i j)))
     (not
      (equal (nth (sac0b-z-to-nat i) p)
             (nth (sac0b-z-to-nat j) p))))))

(defun sac0b-permutation-p (l p)
  (and (integerp l)
       (sac0b-integer-listp p)
       (<= 0 l)
       (<= l (len p))
       (sac0b-permutation-range-p l p)
       (sac0b-permutation-distinct-p l p)))

(defun-sk sac0b-permutation-inverses-p (l p invp)
  (forall i
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i l))
     (and
      (equal
       (nth
        (sac0b-z-to-nat
         (nth (sac0b-z-to-nat i) invp))
        p)
       i)
      (equal
       (nth
        (sac0b-z-to-nat
         (nth (sac0b-z-to-nat i) p))
        invp)
       i)))))

(defun sac0b-permutation-pair-p (l p invp)
  (and (sac0b-permutation-p l p)
       (sac0b-permutation-p l invp)
       (sac0b-permutation-inverses-p l p invp)))

(defun sac0b-valid-chunk-p (array offset length)
  (and (true-listp array)
       (integerp offset)
       (integerp length)
       (<= 0 offset)
       (<= offset (+ offset length))
       (<= (+ offset length) (len array))))

(defun-sk sac0b-copy-elements-p (src dst offset length)
  (forall i
    (implies
     (and (integerp i)
          (<= offset i)
          (< i (+ offset length)))
     (equal
      (nth (sac0b-z-to-nat i) dst)
      (nth (sac0b-z-to-nat i) src)))))

(defun sac0b-copy-p (src dst offset length)
  (and (true-listp src)
       (true-listp dst)
       (integerp offset)
       (integerp length)
       (sac0b-valid-chunk-p src offset length)
       (equal (len src) (len dst))
       (sac0b-copy-elements-p src dst offset length)))

(defun-sk sac0b-copy-to-elements-p
    (src dst source-offset destination-offset length)
  (forall i
    (implies
     (integerp i)
     (and
      (implies
       (and (<= 0 i)
            (< i length))
       (equal
        (nth
         (sac0b-z-to-nat (+ destination-offset i))
         dst)
        (nth
         (sac0b-z-to-nat (+ source-offset i))
         src)))
      (implies
       (and (<= destination-offset i)
            (< i (+ destination-offset length)))
       (equal
        (nth (sac0b-z-to-nat i) dst)
        (nth
         (sac0b-z-to-nat
          (+ i (- source-offset destination-offset)))
         src)))))))

(defun sac0b-copy-to-p
    (src dst source-offset destination-offset length)
  (and (true-listp src)
       (true-listp dst)
       (integerp source-offset)
       (integerp destination-offset)
       (integerp length)
       (sac0b-valid-chunk-p src source-offset length)
       (sac0b-valid-chunk-p dst destination-offset length)
       (equal (len src) (len dst))
       (sac0b-copy-to-elements-p
        src dst source-offset destination-offset length)))

;; The source copy_chunk contract preserves all entries outside the updated
;; interval. OLD is the pre-state array and NEW is the post-state array.
(defun-sk sac0b-frame-p (old new offset length)
  (forall i
    (implies
     (integerp i)
     (and
      (implies
       (and (<= 0 i)
            (< i offset))
       (equal
        (nth (sac0b-z-to-nat i) new)
        (nth (sac0b-z-to-nat i) old)))
      (implies
       (and (<= (+ offset length) i)
            (< i (len new)))
       (equal
        (nth (sac0b-z-to-nat i) new)
        (nth (sac0b-z-to-nat i) old)))))))

(defun-sk sac0b-all-shuffled-chunks-p
    (src dst start sigma k upper)
  (forall j-prime
    (implies
     (and (integerp j-prime)
          (<= 0 j-prime)
          (< j-prime upper))
     (sac0b-copy-p
      src
      dst
      (+ start
         (* (nth (sac0b-z-to-nat j-prime) sigma)
            k))
      k))))

(defun-sk sac0b-all-dst3-steps-p
    (src dst2 start startj sigma k s m j)
  (forall dst3
    (implies
     (and (true-listp dst3)
          (equal (len dst3) (len dst2)))
     (implies
      (and
       (sac0b-copy-to-p src dst3 startj startj k)
       (sac0b-frame-p dst2 dst3 startj k))
      (and
       (sac0b-copy-p src dst3 0 (* s m))
       (sac0b-all-shuffled-chunks-p
        src dst3 start sigma k (+ j 1)))))))

(defun sac0b-j-step-conclusion-p
    (src dst2 start sigma k s m j)
  (and
   (<= 0 j)
   (< j (len sigma))
   (let ((startj
          (+ start
             (* (nth (sac0b-z-to-nat j) sigma)
                k))))
     (and
      (equal (len src) (len dst2))
      (sac0b-valid-chunk-p src startj k)
      (sac0b-valid-chunk-p dst2 startj k)
      (sac0b-all-dst3-steps-p
       src dst2 start startj sigma k s m j)))))

(defun-sk sac0b-all-j-steps-p
    (src dst2 start sigma k s m o2)
  (forall j
    (implies
     (integerp j)
     (implies
      (and
       (<= 0 j)
       (<= j o2)
       (sac0b-copy-p src dst2 0 (* s m))
       (sac0b-all-shuffled-chunks-p
        src dst2 start sigma k j))
      (sac0b-j-step-conclusion-p
       src dst2 start sigma k s m j)))))

(defun sac0b-dst2-body-p
    (src dst2 start sigma k s m o2)
  (and
   (sac0b-all-j-steps-p
    src dst2 start sigma k s m o2)
   (implies
    (and
     (sac0b-copy-p src dst2 0 (* s m))
     (sac0b-all-shuffled-chunks-p
      src dst2 start sigma k (+ o2 1)))
    (sac0b-copy-p src dst2 0 (* (+ s 1) m)))))

(defun-sk sac0b-all-dst2-loops-p
    (src dst1 start sigma k s m o2)
  (forall dst2
    (implies
     (and (true-listp dst2)
          (equal (len dst2) (len dst1)))
     (sac0b-dst2-body-p
      src dst2 start sigma k s m o2))))

(defun sac0b-sigma-body-p
    (src dst1 start sigma k l s m)
  (let ((o2 (- l 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (and
        (sac0b-copy-p src dst1 0 (* s m))
        (sac0b-all-shuffled-chunks-p
         src dst1 start sigma k 0))
       (sac0b-all-dst2-loops-p
        src dst1 start sigma k s m o2)))
     (implies
      (< (+ o2 1) 0)
      (sac0b-copy-p src dst1 0 (* (+ s 1) m))))))

(defun-sk sac0b-all-permutations-p
    (src dst1 start k l s m)
  (forall (sigma invsigma)
    (implies
     (and
      (sac0b-integer-listp sigma)
      (sac0b-integer-listp invsigma)
      (equal (len sigma) (len invsigma))
      (equal (len invsigma) l)
      (sac0b-permutation-pair-p l sigma invsigma))
     (sac0b-sigma-body-p
      src dst1 start sigma k l s m))))

(defun sac0b-s-body-p (src dst1 k l s m)
  (let ((start (* s m)))
    (and
     (< 0 l)
     (sac0b-all-permutations-p
      src dst1 start k l s m))))

(defun-sk sac0b-all-s-loops-p (src dst1 k l m o1)
  (forall s
    (implies
     (integerp s)
     (implies
      (and
       (<= 0 s)
       (<= s o1)
       (sac0b-copy-p src dst1 0 (* s m)))
      (sac0b-s-body-p src dst1 k l s m)))))

(defun-sk sac0b-all-remainder-results-p
    (src old last r full-length)
  (forall new
    (implies
     (and (true-listp new)
          (equal (len new) (len old)))
     (implies
      (and
       (sac0b-copy-to-p src new last last r)
       (sac0b-frame-p old new last r))
      (sac0b-copy-p src new 0 full-length)))))

(defun sac0b-remainder-body-p
    (src old q m r full-length)
  (let ((last (* q m)))
    (and
     (equal (len src) (len old))
     (sac0b-valid-chunk-p src last r)
     (sac0b-valid-chunk-p old last r)
     (sac0b-all-remainder-results-p
      src old last r full-length))))

(defun sac0b-dst1-body-p
    (src dst1 k l q r m o1 full-length)
  (and
   (sac0b-all-s-loops-p src dst1 k l m o1)
   (implies
    (sac0b-copy-p src dst1 0 (* (+ o1 1) m))
    (sac0b-remainder-body-p
     src dst1 q m r full-length))))

(defun-sk sac0b-all-dst1-loops-p
    (src dst k l q r m o1 full-length)
  (forall dst1
    (implies
     (and (true-listp dst1)
          (equal (len dst1) (len dst)))
     (sac0b-dst1-body-p
      src dst1 k l q r m o1 full-length))))

(defun sac0b-main-conclusion-p (src dst k l q r)
  (let* ((m (* k l))
         (o1 (- q 1))
         (full-length (len dst)))
    (and
     (implies
      (<= 0 (+ o1 1))
      (and
       (sac0b-copy-p src dst 0 (* 0 m))
       (sac0b-all-dst1-loops-p
        src dst k l q r m o1 full-length)))
     (implies
      (< (+ o1 1) 0)
      (sac0b-remainder-body-p
       src dst q m r full-length)))))

(defun-sk
  ntp4vc-pearl-verifythis-2024-challenge1-top-smart-array-copy-0b-statement
  ()
  (forall (src dst k l q r)
    (implies
     (and
      (true-listp src)
      (true-listp dst)
      (integerp k)
      (integerp l)
      (integerp q)
      (integerp r)
      (equal (len src) (len dst))
      (< 0 (len dst))
      (< 0 k)
      (< 0 l)
      (<= 0 q)
      (<= 0 r)
      (< r (* k l))
      (equal (len dst)
             (+ (* (* q k) l) r)))
     (sac0b-main-conclusion-p src dst k l q r))))

(value-triple :itpeval-statement-checked)
:q
