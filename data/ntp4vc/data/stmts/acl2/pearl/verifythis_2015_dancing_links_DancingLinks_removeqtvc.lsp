;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2015_dancing_links_DancingLinks_removeqtvc: the dancing
;; links removal verification condition, preserving circular-list structure
;; while unlinking one node by two array updates. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite integer lists represent the Why3 integer arrays and
;; sequences. A tagged record represents the extensional dll type; its
;; predicate includes the complete source type invariant.

(defun dl-remove-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (dl-remove-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun dl-remove-dll-shape-p (record)
  (and
   (true-listp record)
   (equal (len record) 4)
   (equal (car record) :dancing-links-dll)))

(defun dl-remove-prev (record)
  (cadr record))

(defun dl-remove-next (record)
  (caddr record))

(defun dl-remove-n (record)
  (cadddr record))

(defun dl-remove-dll-p (record)
  (and
   (dl-remove-dll-shape-p record)
   (dl-remove-integer-list-p
    (dl-remove-prev record))
   (dl-remove-integer-list-p
    (dl-remove-next record))
   (integerp (dl-remove-n record))
   (equal
    (len (dl-remove-prev record))
    (len (dl-remove-next record)))
   (equal
    (len (dl-remove-next record))
    (dl-remove-n record))))

;; Int.toNat is retained for source list writes. Total integer lookup returns
;; the source inhabited default zero for every negative or out-of-range index.

(defun dl-remove-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun dl-remove-nth-int (xs index)
  (if (and
       (integerp index)
       (<= 0 index))
      (let ((value (nth index xs)))
        (if (integerp value)
            value
          0))
    0))

;; Source List.set leaves the list unchanged when its natural index is outside
;; the list.

(defun dl-remove-list-set-nat (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (dl-remove-list-set-nat
        (cdr xs)
        (- index 1)
        value)))))

(defun dl-remove-list-set (xs index value)
  (dl-remove-list-set-nat
   xs
   (dl-remove-int-to-nat index)
   value))

(defun dl-remove-bounded-index-p (index upper)
  (and
   (integerp index)
   (<= 0 index)
   (< index upper)))

;; The two node-validity predicates are the source definitions verbatim.

(defun dl-remove-valid-in-p (record index)
  (let* ((prev (dl-remove-prev record))
         (next (dl-remove-next record))
         (size (dl-remove-n record))
         (previous-index
          (dl-remove-nth-int prev index))
         (next-index
          (dl-remove-nth-int next index)))
    (and
     (dl-remove-bounded-index-p index size)
     (dl-remove-bounded-index-p
      previous-index size)
     (dl-remove-bounded-index-p
      next-index size)
     (equal
      (dl-remove-nth-int next previous-index)
      index)
     (equal
      (dl-remove-nth-int prev next-index)
      index))))

(defun dl-remove-valid-out-p (record index)
  (let* ((prev (dl-remove-prev record))
         (next (dl-remove-next record))
         (size (dl-remove-n record))
         (previous-index
          (dl-remove-nth-int prev index))
         (next-index
          (dl-remove-nth-int next index)))
    (and
     (dl-remove-bounded-index-p index size)
     (dl-remove-bounded-index-p
      previous-index size)
     (dl-remove-bounded-index-p
      next-index size)
     (equal
      (dl-remove-nth-int next previous-index)
      next-index)
     (equal
      (dl-remove-nth-int prev next-index)
      previous-index))))

;; The inner quantifier enforces pairwise distinct sequence positions.

(defun-sk dl-remove-other-positions-distinct-p
    (sequence index)
  (forall (other-index)
    (implies
     (integerp other-index)
     (implies
      (dl-remove-bounded-index-p
       other-index
       (len sequence))
      (implies
       (not (equal index other-index))
       (not
        (equal
         (dl-remove-nth-int sequence index)
         (dl-remove-nth-int
          sequence other-index))))))))

(defun dl-remove-list-entry-p
    (record sequence index)
  (let* ((entry
          (dl-remove-nth-int sequence index))
         (previous-position
          (if (equal index 0)
              (- (len sequence) 1)
            (- index 1)))
         (next-position
          (if (equal
               index
               (- (len sequence) 1))
              0
            (+ index 1))))
    (and
     (dl-remove-bounded-index-p
      entry
      (dl-remove-n record))
     (equal
      (dl-remove-nth-int
       (dl-remove-prev record)
       entry)
      (dl-remove-nth-int
       sequence
       previous-position))
     (equal
      (dl-remove-nth-int
       (dl-remove-next record)
       entry)
      (dl-remove-nth-int
       sequence
       next-position))
     (dl-remove-other-positions-distinct-p
      sequence index))))

(defun-sk dl-remove-list-entries-p
    (record sequence)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (dl-remove-bounded-index-p
       index
       (len sequence))
      (dl-remove-list-entry-p
       record sequence index)))))

(defun dl-remove-is-list-p (record sequence)
  (and
   (dl-remove-integer-list-p sequence)
   (dl-remove-list-entries-p
    record sequence)))

;; This is extensional equality between integer-indexed lookup after List.set
;; and the generated Function.update antecedent over every integer argument.

(defun-sk dl-remove-set-function-equal-p
    (old index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (dl-remove-nth-int
       (dl-remove-list-set old index value)
       argument)
      (if (equal argument index)
          value
        (dl-remove-nth-int
         old argument))))))

;; L1 retains its internal universal quantifier and source dll type. The two
;; repeated update-length implications are both preserved.

(defun-sk dl-remove-all-result-records-p
    (record index sequence updated-prev
            previous-index next-index)
  (forall (result-record)
    (implies
     (dl-remove-dll-p result-record)
     (let ((updated-next
            (dl-remove-list-set
             (dl-remove-next record)
             previous-index
             next-index)))
       (implies
        (equal
         (len updated-next)
         (len (dl-remove-next record)))
        (implies
         (equal
          (len updated-next)
          (len (dl-remove-next record)))
         (implies
          (dl-remove-set-function-equal-p
           (dl-remove-next record)
           previous-index
           next-index)
          (and
           (and
            (equal
             (len updated-prev)
             (len updated-next))
            (equal
             (len updated-next)
             (dl-remove-n record)))
           (implies
            (and
             (equal
              (dl-remove-n record)
              (dl-remove-n result-record))
             (equal
              updated-next
              (dl-remove-next result-record))
             (equal
              updated-prev
              (dl-remove-prev result-record)))
            (and
             (dl-remove-valid-out-p
              result-record index)
             (dl-remove-is-list-p
              result-record
              sequence)))))))))))

(defun dl-remove-vc-conclusion-p
    (record index sequence)
  (let* ((o1 (dl-remove-prev record))
         (o2 (dl-remove-nth-int o1 index))
         (o3 (dl-remove-next record))
         (o4 (dl-remove-nth-int o3 index))
         (o5 (dl-remove-prev record))
         (updated-prev
          (dl-remove-list-set o5 o4 o2)))
    (and
     (dl-remove-bounded-index-p
      index (len o1))
     (dl-remove-bounded-index-p
      index (len o3))
     (dl-remove-bounded-index-p
      o4 (len o5))
     (implies
      (equal
       (len updated-prev)
       (len o5))
      (implies
       (equal
        (len updated-prev)
        (len (dl-remove-prev record)))
       (implies
        (dl-remove-set-function-equal-p
         o5 o4 o2)
        (and
         (dl-remove-bounded-index-p
          index
          (len (dl-remove-next record)))
         (let* ((o6
                 (dl-remove-nth-int
                  (dl-remove-next record)
                  index))
                (o7
                 (dl-remove-nth-int
                  updated-prev
                  index)))
           (and
            (dl-remove-bounded-index-p
             index
             (len updated-prev))
            (dl-remove-bounded-index-p
             o7
             (len (dl-remove-next record)))
            (dl-remove-all-result-records-p
             record
             index
             sequence
             updated-prev
             o7
             o6))))))))))

;; This closed predicate is the complete unproved remove'vc proposition.

(defun-sk
  ntp4vc-pearl-verifythis-2015-dancing-links-dancinglinks-removeqtvc-statement
  ()
  (forall (record index sequence)
    (implies
     (and
      (dl-remove-dll-p record)
      (integerp index)
      (dl-remove-integer-list-p sequence)
      (dl-remove-valid-in-p
       record index)
      (dl-remove-is-list-p
       record
       (cons index sequence)))
     (dl-remove-vc-conclusion-p
      record index sequence))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
