;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/decrease1_Decrease1_search_recqtvc: the recursive-search verification
;; condition for an integer list whose adjacent values decrease by at most one,
;; including progress and first-zero result specifications. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite proper lists of integers directly represent the
;; source integers and List Z values.  The accessor implements Int.toNat and
;; the source integer-list default value zero.

(defun ntp4vc-decrease1-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-decrease1-integer-list-p (cdr xs)))))

(defun ntp4vc-decrease1-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-decrease1-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-decrease1-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; This is the source decrease1 predicate, retaining its universal
;; quantification over every mathematical integer index.

(defun-sk ntp4vc-decrease1-p (a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (- (len a) 1)))
      (<=
       (- (ntp4vc-decrease1-nth-int index a) 1)
       (ntp4vc-decrease1-nth-int (+ index 1) a))))))

;; The two result alternatives use the same half-open zero-free range as the
;; source VC.

(defun-sk ntp4vc-decrease1-zero-free-range-p
    (a lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (not
       (equal
        (ntp4vc-decrease1-nth-int index a)
        0))))))

(defun ntp4vc-decrease1-result-spec-p
    (a lower result)
  (or
   (and
    (equal result -1)
    (ntp4vc-decrease1-zero-free-range-p
     a lower (len a)))
   (and
    (<= lower result)
    (< result (len a))
    (equal
     (ntp4vc-decrease1-nth-int result a)
     0)
    (ntp4vc-decrease1-zero-free-range-p
     a lower result))))

;; This is the first conjunct of the theorem conclusion.  It preserves the
;; repeated bounds, the positive-value branch, and both explicit termination
;; measure inequalities.

(defun ntp4vc-decrease1-progress-vc-p (a i)
  (implies
   (< i (len a))
   (and
    (and
     (<= 0 i)
     (< i (len a)))
    (implies
     (not
      (equal
       (ntp4vc-decrease1-nth-int i a)
       0))
     (and
      (and
       (<= 0 i)
       (< i (len a)))
      (if
          (<
           0
           (ntp4vc-decrease1-nth-int i a))
          (and
           (and
            (<= 0 i)
            (< i (len a)))
           (let ((o2
                  (+
                   i
                   (ntp4vc-decrease1-nth-int i a))))
             (and
              (and
               (<= 0 (- (len a) i))
               (<
                (- (len a) o2)
                (- (len a) i)))
              (ntp4vc-decrease1-p a)
              (<= 0 o2))))
        (let ((o2 (+ i 1)))
          (and
           (and
            (<= 0 (- (len a) i))
            (<
             (- (len a) o2)
             (- (len a) i)))
           (ntp4vc-decrease1-p a)
           (<= 0 o2)))))))))

;; This is the source conditional premise for a universally quantified result.
;; Recursive-call result specifications remain internal to their two branches.

(defun ntp4vc-decrease1-result-premise-p
    (a i result)
  (if (< i (len a))
      (if
          (equal
           (ntp4vc-decrease1-nth-int i a)
           0)
          (equal result i)
        (if
            (<
             0
             (ntp4vc-decrease1-nth-int i a))
            (let ((o2
                   (+
                    i
                    (ntp4vc-decrease1-nth-int i a))))
              (ntp4vc-decrease1-result-spec-p
               a o2 result))
          (let ((o2 (+ i 1)))
            (ntp4vc-decrease1-result-spec-p
             a o2 result))))
    (equal result -1)))

(defun-sk ntp4vc-decrease1-all-results-p (a i)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (ntp4vc-decrease1-result-premise-p
       a i result)
      (ntp4vc-decrease1-result-spec-p
       a i result)))))

(defun
  ntp4vc-pearl-decrease1-decrease1-search-recqtvc-statement
  (a i)
  (implies
   (and
    (ntp4vc-decrease1-integer-list-p a)
    (integerp i)
    (ntp4vc-decrease1-p a)
    (<= 0 i))
   (and
    (ntp4vc-decrease1-progress-vc-p a i)
    (ntp4vc-decrease1-all-results-p a i))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
