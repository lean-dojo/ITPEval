;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2024_challenge1_Top_smart_array_copy_1qtvc: the
;; verification condition for smart array copying by shuffled subsegments,
;; including permutation, framing, update, and loop-continuation obligations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A conservative carrier predicate and distinguished inhabitant represent
;; the source's arbitrary inhabited element type.  Lists are finite arrays;
;; integer arrays retain a separate explicit element predicate.

(defstub sac-elt-p (value) t)
(defstub sac-elt-default () t)

(defun sac-elt-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (sac-elt-p (car xs))
       (sac-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun sac-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (sac-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun sac-source-context-p ()
  (sac-elt-p (sac-elt-default)))

;; Int.toNat maps negative integers to zero.  The two total indexing
;; operations use the source inhabited defaults outside the finite list.

(defun sac-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun sac-nth-elt (index xs)
  (let ((natural-index (sac-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (sac-elt-default))))

(defun sac-nth-int (index xs)
  (let ((natural-index (sac-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; This is List.set: replace an in-bounds natural position and leave the list
;; unchanged when the position is out of range.

(defun sac-list-set-natural (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (sac-list-set-natural
        (cdr xs)
        (- index 1)
        value)))))

(defun sac-list-set (xs index value)
  (sac-list-set-natural
   xs
   (sac-int-to-nat index)
   value))

;; The Why3 identity function is uniquely determined at every positive length.

(defun sac-identity-build (next remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     next
     (sac-identity-build
      (+ next 1)
      (- remaining 1)))))

(defun sac-identity (length)
  (sac-identity-build 0 (nfix length)))

(defun-sk sac-identity-values-p (array length)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index length))
      (equal
       (sac-nth-int index array)
       index)))))

;; Source predicates over array prefixes and copied chunks.

(defun-sk sac-permutation-p (length permutation)
  (forall (left right)
    (and
     (and
      (<= 0 length)
      (<= length (len permutation)))
     (implies
      (integerp left)
      (implies
       (and
        (<= 0 left)
        (< left length))
       (and
        (<= 0 (sac-nth-int left permutation))
        (< (sac-nth-int left permutation) length))))
     (implies
      (and
       (integerp left)
       (integerp right))
      (implies
       (and
        (<= 0 left)
        (< left length)
        (<= 0 right)
        (< right length)
        (not (equal left right)))
       (not
        (equal
         (sac-nth-int left permutation)
         (sac-nth-int right permutation))))))))

(defun-sk sac-permutation-pair-p (length permutation inverse)
  (forall (index)
    (and
     (sac-permutation-p length permutation)
     (sac-permutation-p length inverse)
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index length))
       (and
        (equal
         (sac-nth-int
          (sac-nth-int index inverse)
          permutation)
         index)
        (equal
         (sac-nth-int
          (sac-nth-int index permutation)
          inverse)
         index)))))))

(defun sac-valid-chunk-p (array offset length)
  (and
   (<= 0 offset)
   (<= offset (+ offset length))
   (<= (+ offset length) (len array))))

(defun-sk sac-copy-p (source destination offset length)
  (forall (index)
    (and
     (sac-valid-chunk-p source offset length)
     (equal (len source) (len destination))
     (implies
      (integerp index)
      (implies
       (and
        (<= offset index)
        (< index (+ offset length)))
       (equal
        (sac-nth-elt index destination)
        (sac-nth-elt index source)))))))

(defun-sk sac-copy-to-p
    (source destination source-offset destination-offset length)
  (forall (index)
    (and
     (sac-valid-chunk-p source source-offset length)
     (sac-valid-chunk-p destination destination-offset length)
     (equal (len source) (len destination))
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index length))
       (equal
        (sac-nth-elt
         (+ destination-offset index)
         destination)
        (sac-nth-elt
         (+ source-offset index)
         source))))
     (implies
      (integerp index)
      (implies
       (and
        (<= destination-offset index)
        (< index (+ destination-offset length)))
       (equal
        (sac-nth-elt index destination)
        (sac-nth-elt
         (+ index (- source-offset destination-offset))
         source)))))))

(defun-sk sac-copy-permutation-p
    (source destination size permutation inverse)
  (forall (index)
    (and
     (sac-valid-chunk-p source 0 size)
     (equal (len source) (len destination))
     (sac-permutation-pair-p size permutation inverse)
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index size))
       (and
        (<= 0 (sac-nth-int index permutation))
        (< (sac-nth-int index permutation) size))))
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index size))
       (and
        (<= 0 (sac-nth-int index inverse))
        (< (sac-nth-int index inverse) size))))
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index size))
       (equal
        (sac-nth-elt index destination)
        (sac-nth-elt
         (sac-nth-int index permutation)
         source))))
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index size))
       (equal
        (sac-nth-elt index source)
        (sac-nth-elt
         (sac-nth-int index inverse)
         destination)))))))

(defun-sk sac-copy-subsegment-p
    (source destination segment chunk-size segment-size subsegment
            sigma tau permutation inverse)
  (forall (index)
    (let* ((start
            (* segment
               (* chunk-size segment-size)))
           (source-start
            (+ start
               (* (sac-nth-int subsegment sigma)
                  chunk-size)))
           (destination-start
            (+ start
               (* (sac-nth-int
                   (sac-nth-int subsegment sigma)
                   tau)
                  chunk-size))))
      (and
       (sac-copy-to-p
        source destination source-start destination-start chunk-size)
       (implies
        (integerp index)
        (implies
         (and
          (<= 0 index)
          (< index chunk-size))
         (equal
          (sac-nth-int
           (+ destination-start index)
           permutation)
          (+ source-start index))))
       (implies
        (integerp index)
        (implies
         (and
          (<= 0 index)
          (< index chunk-size))
         (equal
          (sac-nth-int
           (+ source-start index)
           inverse)
          (+ destination-start index))))))))

(defun-sk sac-frame-p (before after offset length)
  (forall (index)
    (and
     (equal (len after) (len before))
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index offset))
       (equal
        (nth (sac-int-to-nat index) after)
        (nth (sac-int-to-nat index) before))))
     (implies
      (integerp index)
      (implies
       (and
        (<= (+ offset length) index)
        (< index (len after)))
       (equal
        (nth (sac-int-to-nat index) after)
        (nth (sac-int-to-nat index) before)))))))

;; Reusable universally quantified invariant fragments.

(defun-sk sac-all-subsegments-before-p
    (source destination segment chunk-size segment-size upper
            sigma tau permutation inverse)
  (forall (subsegment)
    (implies
     (integerp subsegment)
     (implies
      (and
       (<= 0 subsegment)
       (< subsegment upper))
      (sac-copy-subsegment-p
       source destination segment chunk-size segment-size subsegment
       sigma tau permutation inverse)))))

(defun-sk sac-index-prefix-p
    (array index-base value-base upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (equal
       (sac-nth-int (+ index-base index) array)
       (+ value-base index))))))

;; Extensional forms of the three source equalities between a List.set view
;; and Function.update.

(defun-sk sac-elt-list-set-update-p (array index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (sac-nth-elt
       argument
       (sac-list-set array index value))
      (if (equal argument index)
          value
        (sac-nth-elt argument array))))))

(defun-sk sac-int-list-set-update-p (array index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (sac-nth-int
       argument
       (sac-list-set array index value))
      (if (equal argument index)
          value
        (sac-nth-int argument array))))))

;; One body iteration of the innermost chunk-copy loop.

(defun sac-inner-update-result-p
    (source destination-before destination
            permutation-before permutation
            inverse-before inverse
            segment chunk-size segment-size subsegment
            sigma tau segment-width source-start destination-start index)
  (let* ((source-index (+ source-start index))
         (element (sac-nth-elt source-index source))
         (destination-index (+ destination-start index))
         (destination-next
          (sac-list-set destination destination-index element))
         (permutation-value (+ source-start index))
         (permutation-index (+ destination-start index))
         (permutation-next
          (sac-list-set
           permutation permutation-index permutation-value))
         (inverse-value (+ destination-start index))
         (inverse-index (+ source-start index))
         (inverse-next
          (sac-list-set inverse inverse-index inverse-value)))
    (and
     (and
      (<= 0 source-index)
      (< source-index (len source)))
     (and
      (<= 0 destination-index)
      (< destination-index (len destination)))
     (implies
      (equal
       (len destination-next)
       (len destination))
      (implies
       (sac-elt-list-set-update-p
        destination destination-index element)
       (and
        (and
         (<= 0 permutation-index)
         (< permutation-index (len permutation)))
        (implies
         (equal
          (len permutation-next)
          (len permutation))
         (implies
          (sac-int-list-set-update-p
           permutation permutation-index permutation-value)
          (and
           (and
            (<= 0 inverse-index)
            (< inverse-index (len inverse)))
           (implies
            (equal
             (len inverse-next)
             (len inverse))
            (implies
             (sac-int-list-set-update-p
              inverse inverse-index inverse-value)
             (and
              (sac-frame-p
               destination-before destination-next
               destination-start chunk-size)
              (sac-frame-p
               permutation-before permutation-next
               destination-start chunk-size)
              (sac-frame-p
               inverse-before inverse-next
               source-start chunk-size)
              (sac-permutation-pair-p
               (* segment segment-width)
               permutation-next inverse-next)
              (sac-copy-permutation-p
               source destination-next
               (* segment segment-width)
               permutation-next inverse-next)
              (sac-copy-to-p
               source destination-next
               source-start destination-start (+ index 1))
              (sac-index-prefix-p
               permutation-next destination-start source-start
               (+ index 1))
              (sac-index-prefix-p
               inverse-next source-start destination-start
               (+ index 1))
              (sac-all-subsegments-before-p
               source destination-next segment chunk-size segment-size
               subsegment sigma tau permutation-next inverse-next)))))))))))))

(defun-sk sac-all-inner-indices-p
    (source destination-before destination
            permutation-before permutation
            inverse-before inverse
            segment chunk-size segment-size subsegment
            sigma tau segment-width source-start destination-start upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (and
        (<= 0 index)
        (<= index upper))
       (sac-frame-p
        destination-before destination destination-start chunk-size)
       (sac-frame-p
        permutation-before permutation destination-start chunk-size)
       (sac-frame-p
        inverse-before inverse source-start chunk-size)
       (sac-permutation-pair-p
        (* segment segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination (* segment segment-width) permutation inverse)
       (sac-copy-to-p
        source destination source-start destination-start index)
       (sac-index-prefix-p
        permutation destination-start source-start index)
       (sac-index-prefix-p
        inverse source-start destination-start index)
       (sac-all-subsegments-before-p
        source destination segment chunk-size segment-size subsegment
        sigma tau permutation inverse))
      (sac-inner-update-result-p
       source destination-before destination
       permutation-before permutation
       inverse-before inverse
       segment chunk-size segment-size subsegment
       sigma tau segment-width source-start destination-start index)))))

(defun-sk sac-all-inner-states-p
    (source destination-before permutation-before inverse-before
            segment chunk-size segment-size subsegment sigma tau
            segment-width source-start destination-start upper)
  (forall (inverse permutation destination)
    (implies
     (and
      (sac-integer-list-p inverse)
      (sac-integer-list-p permutation)
      (sac-elt-list-p destination))
     (implies
      (equal (len inverse) (len inverse-before))
      (implies
       (equal (len permutation) (len permutation-before))
       (implies
        (equal (len destination) (len destination-before))
        (and
         (sac-all-inner-indices-p
          source destination-before destination
          permutation-before permutation
          inverse-before inverse
          segment chunk-size segment-size subsegment sigma tau
          segment-width source-start destination-start upper)
         (implies
          (and
           (sac-frame-p
            destination-before destination destination-start chunk-size)
           (sac-frame-p
            permutation-before permutation destination-start chunk-size)
           (sac-frame-p
            inverse-before inverse source-start chunk-size)
           (sac-permutation-pair-p
            (* segment segment-width) permutation inverse)
           (sac-copy-permutation-p
            source destination
            (* segment segment-width) permutation inverse)
           (sac-copy-to-p
            source destination source-start destination-start (+ upper 1))
           (sac-index-prefix-p
            permutation destination-start source-start (+ upper 1))
           (sac-index-prefix-p
            inverse source-start destination-start (+ upper 1))
           (sac-all-subsegments-before-p
            source destination segment chunk-size segment-size subsegment
            sigma tau permutation inverse))
          (and
           (sac-permutation-pair-p
            (* segment segment-width) permutation inverse)
           (sac-copy-permutation-p
            source destination
            (* segment segment-width) permutation inverse)
           (sac-all-subsegments-before-p
            source destination segment chunk-size segment-size
            (+ subsegment 1) sigma tau permutation inverse))))))))))

(defun sac-inner-loop-vc-p
    (source destination permutation inverse
            segment chunk-size segment-size subsegment sigma tau
            segment-width source-start destination-start)
  (let ((upper (- chunk-size 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sac-frame-p
        destination destination destination-start chunk-size)
       (sac-frame-p
        permutation permutation destination-start chunk-size)
       (sac-frame-p
        inverse inverse source-start chunk-size)
       (sac-permutation-pair-p
        (* segment segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* segment segment-width) permutation inverse)
       (sac-copy-to-p
        source destination source-start destination-start 0)
       (sac-index-prefix-p permutation destination-start source-start 0)
       (sac-index-prefix-p inverse source-start destination-start 0)
       (sac-all-subsegments-before-p
        source destination segment chunk-size segment-size subsegment
        sigma tau permutation inverse)
       (sac-all-inner-states-p
        source destination permutation inverse
        segment chunk-size segment-size subsegment sigma tau
        segment-width source-start destination-start upper)))
     (implies
      (< (+ upper 1) 0)
      (and
       (sac-permutation-pair-p
        (* segment segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* segment segment-width) permutation inverse)
       (sac-all-subsegments-before-p
        source destination segment chunk-size segment-size
        (+ subsegment 1) sigma tau permutation inverse))))))

;; One iteration and all states of the subsegment loop.

(defun sac-subsegment-step-result-p
    (source destination permutation inverse
            segment chunk-size segment-size subsegment
            sigma tau segment-width start)
  (and
   (and
    (<= 0 subsegment)
    (< subsegment (len sigma)))
   (let ((source-start
          (+ start
             (* (sac-nth-int subsegment sigma)
                chunk-size))))
     (and
      (and
       (<= 0 subsegment)
       (< subsegment (len sigma)))
      (let ((sigma-value
             (sac-nth-int subsegment sigma)))
        (and
         (and
          (<= 0 sigma-value)
          (< sigma-value (len tau)))
         (let ((destination-start
                (+ start
                   (* (sac-nth-int sigma-value tau)
                      chunk-size))))
           (sac-inner-loop-vc-p
            source destination permutation inverse
            segment chunk-size segment-size subsegment sigma tau
            segment-width source-start destination-start))))))))

(defun-sk sac-all-subsegment-indices-p
    (source destination permutation inverse
            segment chunk-size segment-size sigma tau
            segment-width start upper)
  (forall (subsegment)
    (implies
     (integerp subsegment)
     (implies
      (and
       (and
        (<= 0 subsegment)
        (<= subsegment upper))
       (sac-permutation-pair-p
        (* segment segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* segment segment-width) permutation inverse)
       (sac-all-subsegments-before-p
        source destination segment chunk-size segment-size subsegment
        sigma tau permutation inverse))
      (sac-subsegment-step-result-p
       source destination permutation inverse
       segment chunk-size segment-size subsegment
       sigma tau segment-width start)))))

(defun-sk sac-all-subsegment-states-p
    (source destination-before permutation-before inverse-before
            segment chunk-size segment-size sigma tau
            segment-width start upper)
  (forall (inverse permutation destination)
    (implies
     (and
      (sac-integer-list-p inverse)
      (sac-integer-list-p permutation)
      (sac-elt-list-p destination))
     (implies
      (equal (len inverse) (len inverse-before))
      (implies
       (equal (len permutation) (len permutation-before))
       (implies
        (equal (len destination) (len destination-before))
        (and
         (sac-all-subsegment-indices-p
          source destination permutation inverse
          segment chunk-size segment-size sigma tau
          segment-width start upper)
         (implies
          (and
           (sac-permutation-pair-p
            (* segment segment-width) permutation inverse)
           (sac-copy-permutation-p
            source destination
            (* segment segment-width) permutation inverse)
           (sac-all-subsegments-before-p
            source destination segment chunk-size segment-size (+ upper 1)
            sigma tau permutation inverse))
          (and
           (sac-permutation-pair-p
            (* (+ segment 1) segment-width) permutation inverse)
           (sac-copy-permutation-p
            source destination
            (* (+ segment 1) segment-width) permutation inverse))))))))))

(defun sac-tau-loop-vc-p
    (source destination permutation inverse
            segment chunk-size segment-size sigma tau segment-width)
  (let ((upper (- segment-size 1))
        (start (* segment segment-width)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sac-permutation-pair-p
        (* segment segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* segment segment-width) permutation inverse)
       (sac-all-subsegments-before-p
        source destination segment chunk-size segment-size 0
        sigma tau permutation inverse)
       (sac-all-subsegment-states-p
        source destination permutation inverse
        segment chunk-size segment-size sigma tau
        segment-width start upper)))
     (implies
      (< (+ upper 1) 0)
      (and
       (sac-permutation-pair-p
        (* (+ segment 1) segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* (+ segment 1) segment-width) permutation inverse))))))

(defun-sk sac-all-tau-permutations-p
    (source destination permutation inverse
            segment chunk-size segment-size sigma segment-width)
  (forall (tau inverse-tau)
    (implies
     (and
      (sac-integer-list-p tau)
      (sac-integer-list-p inverse-tau))
     (implies
      (and
       (equal (len tau) (len inverse-tau))
       (equal (len inverse-tau) segment-size)
       (sac-permutation-pair-p segment-size tau inverse-tau))
      (sac-tau-loop-vc-p
       source destination permutation inverse
       segment chunk-size segment-size sigma tau segment-width)))))

(defun-sk sac-all-sigma-permutations-p
    (source destination permutation inverse
            segment chunk-size segment-size segment-width)
  (forall (sigma inverse-sigma)
    (implies
     (and
      (sac-integer-list-p sigma)
      (sac-integer-list-p inverse-sigma))
     (implies
      (and
       (equal (len sigma) (len inverse-sigma))
       (equal (len inverse-sigma) segment-size)
       (sac-permutation-pair-p
        segment-size sigma inverse-sigma))
      (and
       (< 0 segment-size)
       (sac-all-tau-permutations-p
        source destination permutation inverse
        segment chunk-size segment-size sigma segment-width))))))

(defun sac-segment-step-result-p
    (source destination permutation inverse
            segment chunk-size segment-size segment-width)
  (and
   (< 0 segment-size)
   (sac-all-sigma-permutations-p
    source destination permutation inverse
    segment chunk-size segment-size segment-width)))

(defun-sk sac-all-segment-indices-p
    (source destination permutation inverse
            chunk-size segment-size segment-width upper)
  (forall (segment)
    (implies
     (integerp segment)
     (implies
      (and
       (and
        (<= 0 segment)
        (<= segment upper))
       (sac-permutation-pair-p
        (* segment segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* segment segment-width) permutation inverse))
      (sac-segment-step-result-p
       source destination permutation inverse
       segment chunk-size segment-size segment-width)))))

;; The final remainder-copy loop.

(defun sac-tail-step-result-p
    (source destination permutation inverse last index)
  (let* ((source-index (+ last index))
         (element (sac-nth-elt source-index source))
         (destination-index (+ last index))
         (destination-next
          (sac-list-set destination destination-index element))
         (permutation-value (+ last index))
         (permutation-index (+ last index))
         (permutation-next
          (sac-list-set
           permutation permutation-index permutation-value))
         (inverse-value (+ last index))
         (inverse-index (+ last index))
         (inverse-next
          (sac-list-set inverse inverse-index inverse-value)))
    (and
     (and
      (<= 0 source-index)
      (< source-index (len source)))
     (and
      (<= 0 destination-index)
      (< destination-index (len destination)))
     (implies
      (equal
       (len destination-next)
       (len destination))
      (implies
       (sac-elt-list-set-update-p
        destination destination-index element)
       (and
        (and
         (<= 0 permutation-index)
         (< permutation-index (len permutation)))
        (implies
         (equal
          (len permutation-next)
          (len permutation))
         (implies
          (sac-int-list-set-update-p
           permutation permutation-index permutation-value)
          (and
           (and
            (<= 0 inverse-index)
            (< inverse-index (len inverse)))
           (implies
            (equal
             (len inverse-next)
             (len inverse))
            (implies
             (sac-int-list-set-update-p
              inverse inverse-index inverse-value)
             (and
              (sac-permutation-pair-p
               (+ last (+ index 1))
               permutation-next inverse-next)
              (sac-copy-permutation-p
               source destination-next
               (+ last (+ index 1))
               permutation-next inverse-next)))))))))))))

(defun-sk sac-all-tail-indices-p
    (source destination permutation inverse last upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (and
        (<= 0 index)
        (<= index upper))
       (sac-permutation-pair-p
        (+ last index) permutation inverse)
       (sac-copy-permutation-p
        source destination (+ last index) permutation inverse))
      (sac-tail-step-result-p
       source destination permutation inverse last index)))))

(defun-sk sac-all-tail-states-p
    (source destination-before permutation-before inverse-before
            last upper total-length)
  (forall (inverse permutation destination)
    (implies
     (and
      (sac-integer-list-p inverse)
      (sac-integer-list-p permutation)
      (sac-elt-list-p destination))
     (implies
      (equal (len inverse) (len inverse-before))
      (implies
       (equal (len permutation) (len permutation-before))
       (implies
        (equal (len destination) (len destination-before))
        (and
         (sac-all-tail-indices-p
          source destination permutation inverse last upper)
         (implies
          (and
           (sac-permutation-pair-p
            (+ last (+ upper 1)) permutation inverse)
           (sac-copy-permutation-p
            source destination
            (+ last (+ upper 1)) permutation inverse))
          (sac-copy-permutation-p
           source destination total-length permutation inverse)))))))))

(defun sac-tail-vc-p
    (source destination permutation inverse last remainder total-length)
  (let ((upper (- remainder 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sac-permutation-pair-p
        (+ last 0) permutation inverse)
       (sac-copy-permutation-p
        source destination (+ last 0) permutation inverse)
       (sac-all-tail-states-p
        source destination permutation inverse
        last upper total-length)))
     (implies
      (< (+ upper 1) 0)
      (sac-copy-permutation-p
       source destination total-length permutation inverse)))))

;; Every admissible state of the outer segment loop, followed by its exit
;; continuation into the final remainder-copy loop.

(defun-sk sac-all-outer-states-p
    (source destination-before permutation-before inverse-before
            chunk-size segment-size quotient remainder
            segment-width upper total-length)
  (forall (inverse permutation destination)
    (implies
     (and
      (sac-integer-list-p inverse)
      (sac-integer-list-p permutation)
      (sac-elt-list-p destination))
     (implies
      (equal (len inverse) (len inverse-before))
      (implies
       (equal (len permutation) (len permutation-before))
       (implies
        (equal (len destination) (len destination-before))
        (and
         (sac-all-segment-indices-p
          source destination permutation inverse
          chunk-size segment-size segment-width upper)
         (implies
          (and
           (sac-permutation-pair-p
            (* (+ upper 1) segment-width)
            permutation inverse)
           (sac-copy-permutation-p
            source destination
            (* (+ upper 1) segment-width)
            permutation inverse))
          (sac-tail-vc-p
           source destination permutation inverse
           (* quotient segment-width)
           remainder total-length)))))))))

(defun sac-outer-loop-vc-p
    (source destination permutation inverse
            chunk-size segment-size quotient remainder total-length)
  (let ((segment-width (* chunk-size segment-size))
        (upper (- quotient 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sac-permutation-pair-p
        (* 0 segment-width) permutation inverse)
       (sac-copy-permutation-p
        source destination
        (* 0 segment-width) permutation inverse)
       (sac-all-outer-states-p
        source destination permutation inverse
        chunk-size segment-size quotient remainder
        segment-width upper total-length)))
     (implies
      (< (+ upper 1) 0)
      (sac-tail-vc-p
       source destination permutation inverse
       (* quotient segment-width)
       remainder total-length)))))

;; The complete unproved verification condition.  Typed binders, all eight
;; named hypotheses, both identity-array antecedents, and every nested
;; universal continuation from the source VC remain explicit.

(defun
    ntp4vc-pearl-verifythis-2024-challenge1-top-smart-array-copy-1qtvc-statement
    (source destination chunk-size segment-size quotient remainder)
  (implies
   (and
    (sac-source-context-p)
    (sac-elt-list-p source)
    (sac-elt-list-p destination)
    (integerp chunk-size)
    (integerp segment-size)
    (integerp quotient)
    (integerp remainder)
    (equal (len source) (len destination))
    (< 0 (len destination))
    (< 0 chunk-size)
    (< 0 segment-size)
    (<= 0 quotient)
    (<= 0 remainder)
    (< remainder (* chunk-size segment-size))
    (equal
     (len destination)
     (+ (* quotient chunk-size segment-size)
        remainder)))
   (and
    (< 0 (len destination))
    (let* ((total-length (len destination))
           (permutation (sac-identity total-length)))
      (implies
       (and
        (equal (len permutation) (len destination))
        (sac-identity-values-p permutation total-length)
        (sac-permutation-pair-p
         total-length permutation permutation))
       (and
        (< 0 (len destination))
        (let ((inverse (sac-identity total-length)))
          (implies
           (and
            (equal (len inverse) (len destination))
            (sac-identity-values-p inverse total-length)
            (sac-permutation-pair-p
             total-length inverse inverse))
           (sac-outer-loop-vc-p
            source destination permutation inverse
            chunk-size segment-size quotient remainder
            total-length)))))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
