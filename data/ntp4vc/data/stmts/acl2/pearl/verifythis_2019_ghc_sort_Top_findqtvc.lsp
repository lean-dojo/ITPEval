;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_findqtvc: the recursive verification
;; condition for finding an integer value in a nonempty half-open sequence
;; interval with a positive occurrence count. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite lists of ACL2 integers represent Why3 sequences of
;; mathematical integers without bounding their lengths or element values.

(defun ghc-find-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ghc-find-integer-list-p (cdr xs)))
    (equal xs nil)))

;; These total list operations implement the source half-open interval
;; seq[lower..upper] as take(upper-lower, drop(lower, seq)).

(defun ghc-find-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (ghc-find-drop
     (- count 1)
     (cdr xs))))

(defun ghc-find-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (ghc-find-take
      (- count 1)
      (cdr xs)))))

(defun ghc-find-count-occurrences (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (if (equal value (car xs)) 1 0)
     (ghc-find-count-occurrences
      value
      (cdr xs)))))

(defun ghc-find-interval-occurrences
    (value seq lower upper)
  (ghc-find-count-occurrences
   value
   (ghc-find-take
    (- upper lower)
    (ghc-find-drop lower seq))))

;; Why3 sequence reads in this VC are in bounds. The zero default makes the
;; ACL2 representation total while agreeing with every active source branch.

(defun ghc-find-nth-zero (index seq)
  (if (and
       (integerp index)
       (<= 0 index)
       (< index (len seq)))
      (nth index seq)
    0))

(defun ghc-find-recursive-call-obligation-p
    (seq value start finish)
  (let ((next-start (+ start 1)))
    (and
     (and
      (<= 0 (- finish start))
      (< (- finish next-start)
         (- finish start)))
     (and
      (<= 0 next-start)
      (< next-start finish)
      (<= finish (len seq)))
     (<=
      1
      (ghc-find-interval-occurrences
       value seq next-start finish)))))

(defun ghc-find-result-premise-p
    (seq value start finish first result)
  (if (equal first value)
      (equal result start)
    (and
     (<= (+ start 1) result)
     (< result finish)
     (equal
      (ghc-find-nth-zero result seq)
      value))))

(defun ghc-find-result-postcondition-p
    (seq value start finish result)
  (and
   (<= start result)
   (< result finish)
   (equal
    (ghc-find-nth-zero result seq)
    value)))

;; RESULT remains universally quantified inside the statement, as in the
;; generated recursive-call verification condition.

(defun-sk ghc-find-all-results-correct-p
    (seq value start finish first)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (ghc-find-result-premise-p
       seq value start finish first result)
      (ghc-find-result-postcondition-p
       seq value start finish result)))))

(defun
    ntp4vc-pearl-verifythis-2019-ghc-sort-top-findqtvc-statement
    (start finish seq value)
  (implies
   (and
    (integerp start)
    (integerp finish)
    (ghc-find-integer-list-p seq)
    (integerp value)
    (<= 0 start)
    (< start finish)
    (<= finish (len seq))
    (<=
     1
     (ghc-find-interval-occurrences
      value seq start finish)))
   (let ((first
          (ghc-find-nth-zero start seq)))
     (and
      (implies
       (not (equal first value))
       (ghc-find-recursive-call-obligation-p
        seq value start finish))
      (ghc-find-all-results-correct-p
       seq value start finish first)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
