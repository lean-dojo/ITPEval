;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc:
;; the verification condition for copying an integer array into a finite
;; sequence while preserving length and every indexed value. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 arrays and finite sequences of mathematical integers are represented
;; bijectively by proper ACL2 lists of unbounded ACL2 integers.

(defun lp-to-seq-int-list-p (sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (and
       (integerp (car sequence))
       (lp-to-seq-int-list-p (cdr sequence)))
    (equal sequence nil)))

;; Integer indexing follows Int.toNat and uses the exported inhabited integer
;; value zero outside the finite list. Every non-vacuous source access is
;; guarded by its original in-bounds condition.

(defun lp-to-seq-read-nat (index sequence)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (< 0 index)
       (consp sequence))
      (lp-to-seq-read-nat (- index 1) (cdr sequence))
    (if (consp sequence) (car sequence) 0)))

(defun lp-to-seq-read (sequence index)
  (lp-to-seq-read-nat (nfix index) sequence))

;; This is the source loop invariant
;;   forall i. 0 <= i < bound -> sequence[i] = array[i].

(defun-sk lp-to-seq-prefix-copy-p (sequence array bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound))
      (equal
       (lp-to-seq-read sequence index)
       (lp-to-seq-read array index))))))

;; The source snoc operation has exactly these length, last-element, and
;; old-prefix properties.

(defun-sk lp-to-seq-snoc-prefix-p (old new)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len old)))
      (equal
       (lp-to-seq-read new index)
       (lp-to-seq-read old index))))))

(defun lp-to-seq-snoc-spec-p (old added new)
  (and
   (equal (len new) (+ 1 (len old)))
   (equal
    (lp-to-seq-read new (len old))
    added)
   (lp-to-seq-snoc-prefix-p old new)))

;; Preservation of the two source loop invariants through one snoc step.

(defun lp-to-seq-step-p (array o1 sequence)
  (implies
   (and
    (<= 0 (len sequence))
    (<= (len sequence) o1)
    (lp-to-seq-prefix-copy-p
     sequence array (len sequence)))
   (and
    (<= 0 (len sequence))
    (< (len sequence) (len array))
    (let* ((added
            (lp-to-seq-read array (len sequence)))
           (extended
            (append sequence (list added))))
      (implies
       (lp-to-seq-snoc-spec-p
        sequence added extended)
       (and
        (equal
         (len extended)
         (+ (len sequence) 1))
        (lp-to-seq-prefix-copy-p
         extended array (+ (len sequence) 1))))))))

;; The loop exit obligation turns k = length(array) into the function's two
;; postconditions.

(defun lp-to-seq-exit-p (array o1 sequence)
  (implies
   (and
    (equal (len sequence) (+ o1 1))
    (lp-to-seq-prefix-copy-p
     sequence array (+ o1 1)))
   (and
    (equal (len sequence) (len array))
    (lp-to-seq-prefix-copy-p
     sequence array (len sequence)))))

(defun-sk lp-to-seq-all-loop-obligations-p (array o1)
  (forall (sequence)
    (implies
     (lp-to-seq-int-list-p sequence)
     (and
      (lp-to-seq-step-p array o1 sequence)
      (lp-to-seq-exit-p array o1 sequence)))))

;; This preserves the generated split between the nonempty loop range and the
;; impossible negative-range branch.

(defun lp-to-seq-vc-p (array)
  (let ((o1 (- (len array) 1)))
    (and
     (implies
      (<= 0 (+ o1 1))
      (and
       (and
        (equal (len nil) 0)
        (lp-to-seq-prefix-copy-p nil array 0))
       (lp-to-seq-all-loop-obligations-p
        array o1)))
     (implies
      (< (+ o1 1) 0)
      (let ((result nil))
        (and
         (equal (len result) (len array))
         (lp-to-seq-prefix-copy-p
          result array (len result))))))))

(defun
    ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-to-seqqtvc-statement
    (array)
  (implies
   (lp-to-seq-int-list-p array)
   (lp-to-seq-vc-p array)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
