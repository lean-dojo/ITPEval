;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/word_common_factor_Top_common_factorqtvc: the common-word-factor
;; verification condition for two commuting words, including recursive-call
;; descent and nonnegative power representations. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; character type. Lists satisfying WCF-WORD-P are exactly the finite words
;; over that unbounded, non-enumerated carrier.

(defstub wcf-char-p (value) t)
(defstub wcf-default-char () t)

(defun wcf-word-p (word)
  (declare (xargs :measure (acl2-count word)))
  (if (consp word)
      (and
       (wcf-char-p (car word))
       (wcf-word-p (cdr word)))
    (equal word nil)))

(defun wcf-source-context-p ()
  (wcf-char-p (wcf-default-char)))

;; This is the source recursive word power on its required domain n >= 0.
;; The nil branch for other ACL2 objects is only a total extension outside
;; that typed source domain.

(defun wcf-power (word n)
  (declare (xargs :measure (nfix n)))
  (if (and
       (integerp n)
       (< 0 n))
      (append
       word
       (wcf-power word (- n 1)))
    nil))

;; Preserve the generated recursive-call descent conjunct, including the
;; source slice c = drop(length(a), b), every explicit bound, and the
;; impossible-looking alternate disjunct emitted by the VC generator.

(defun wcf-descent-vc-p (a b)
  (implies
   (not (equal (len a) 0))
   (implies
    (not (equal (len b) 0))
    (if (<= (len a) (len b))
        (let* ((o2 (len a))
               (c (nthcdr o2 b)))
          (and
           (and
            (<= 0 o2)
            (<= o2 (len b)))
           (and
            (equal b (append a c))
            (implies
             (equal b (append a c))
             (and
              (and
               (<= 0 (len b))
               (< (len c) (len b)))
              (equal
               (append a c)
               (append c a)))))))
      (and
       (or
        (and
         (<= 0 (len a))
         (< (len b) (len a)))
        (and
         (equal (len a) (len b))
         (<= 0 (len b))
         (< (len a) (len b))))
       (equal
        (append b a)
        (append a b)))))))

;; This existential remains internal to the length(a) <= length(b) branch.

(defun-sk wcf-kb1-exists-p (a c w ka kb)
  (exists (kb1)
    (and
     (integerp kb1)
     (and
      (and
       (and
        (<= 0 ka)
        (equal a (wcf-power w ka)))
       (and
        (<= 0 kb1)
        (equal c (wcf-power w kb1))))
      (equal kb (+ ka kb1))))))

;; This is exactly the conditional equation constraining a possible result
;; triple (w, ka, kb) of the recursive common-factor computation.

(defun wcf-result-premise-p (a b w ka kb)
  (if (equal (len a) 0)
      (and
       (equal w b)
       (equal ka 0)
       (equal kb 1))
    (if (equal (len b) 0)
        (and
         (equal w a)
         (equal ka 1)
         (equal kb 0))
      (if (<= (len a) (len b))
          (let ((c (nthcdr (len a) b)))
            (and
             (equal b (append a c))
             (wcf-kb1-exists-p
              a c w ka kb)))
        (and
         (and
          (<= 0 kb)
          (equal b (wcf-power w kb)))
         (and
          (<= 0 ka)
          (equal a (wcf-power w ka))))))))

(defun wcf-result-postcondition-p (a b w ka kb)
  (and
   (and
    (<= 0 ka)
    (equal a (wcf-power w ka)))
   (and
    (<= 0 kb)
    (equal b (wcf-power w kb)))))

;; Preserve the source universal quantification over every typed candidate
;; word and both mathematical-integer exponents.

(defun-sk wcf-all-results-p (a b)
  (forall (w ka kb)
    (implies
     (and
      (wcf-word-p w)
      (integerp ka)
      (integerp kb))
     (implies
      (wcf-result-premise-p
       a b w ka kb)
      (wcf-result-postcondition-p
       a b w ka kb)))))

;; The outer quantifier represents the source theorem's arbitrary words a and
;; b. Its antecedent is exactly their typing, the inhabited source context,
;; and the sole theorem assumption a ++ b = b ++ a.

(defun-sk
  ntp4vc-pearl-word-common-factor-top-common-factorqtvc-statement
  ()
  (forall (a b)
    (implies
     (and
      (wcf-source-context-p)
      (wcf-word-p a)
      (wcf-word-p b)
      (equal
       (append a b)
       (append b a)))
     (and
      (wcf-descent-vc-p a b)
      (wcf-all-results-p a b)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
