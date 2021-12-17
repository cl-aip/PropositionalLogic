;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*- File logic/prop.lisp

;;;; Propositional Logic

   
(defstruct prop-kb
  "A simple KB implementation that builds a big conjoined sentence."
  ;; The sentence slot will be, e.g., (and P (not Q) R (or S T) ...)
  (sentence (make-exp 'and)))

(defstruct truth-table
  atomics              ; The propositional atomics
  sentences            ; Sentences that head the columns
  rows                 ; Lists of t or nil truth values
  )

;;;; Tell, Ask, and Retract

(defmethod tell ((kb prop-kb) sentence)
  "Add a sentence to a propositional knowledge base."
  (push (logic sentence) (args (prop-kb-sentence kb)))
  t)

(defmethod ask-each ((kb prop-kb) query fn)
  "Ask a propositional knowledge base if the query is entailed by the kb."
  (when (eq (validity (make-exp '=> (prop-kb-sentence kb) (logic query)))
	    'valid)
    (funcall fn +no-bindings+)))

(defmethod retract ((kb prop-kb) sentence)
  "Remove a sentence from a knowledge base."
  ;; This only retracts sentences that were explicitly told to the kb.
  (deletef sentence (args (prop-kb-sentence kb)) :test #'equal)
  t)

;;;; Other Useful Top-Level Functions

(defun validity (sentence)
  "Return either VALID, SATISFIABLE or UNSATISFIABLE."
  (let* ((table (build-truth-table (logic sentence) :short t))
	 (rows (truth-table-rows table)))
    (cond ((every #'last1 rows) 'valid)
	  ((some #'last1 rows) 'satisfiable)
          (t 'unsatisfiable))))

(defun truth-table (sentence)
  "Build and print a truth table for this sentence, with columns for all the
  propositions and all the non-trivial component sentences.  If the sentence
  is valid, the last column will have all T's.
  Example: (truth-table '(equiv P (not (not P))))."
  (print-truth-table (build-truth-table (logic sentence))))

;;;; Auxiliary Functions

(defun interp (sentence &optional interpretation)
  "Evaluate the truth of the sentence under an interpretation.
  The interpretation is a list of (proposition . truth-value) pairs,
  where a truth-value is t or nil, e.g., ((P . t) (Q . nil)).
  It is an error if there are any propositional atomics in the sentence
  that are not given a value in the interpretation."
  (cond (interpretation (interp (sublis interpretation sentence :test #'equal) nil))
        ((eq sentence 't) t)
        ((eq sentence 'nil) nil)
        ((atom sentence) (error "No interpretation for ~A." sentence))
        (t (case (op sentence)
             (or  (some #'interp (args sentence)))
             (and (every #'interp (args sentence)))
             (not (not (interp (arg1 sentence))))
             (imply (or (interp (arg2 sentence))
                        (not (interp (arg1 sentence)))))
             (equiv (eq (interp (arg1 sentence))
                        (interp (arg2 sentence))))
             (otherwise (error "Unknown connective ~A in ~A"
                          (op sentence) sentence))))))

;; Note: a more efficient implementation of interpretations would be
;; a sequence of n propositional symbols and a number from 0 to (2^n)-1.
;; Symbol i is true iff bit i in the number is 1.

;;;; Truth Tables

(defun build-truth-table (sentence &key short)
  "Build a truth table whose last column is the sentence.  If SHORT is true,
  then that is the only column. If SHORT is false, all the sub-sentences
  are also included as columns (except constants)."
  (let* ((atomics (prop-atomics-in sentence))
	 (sentences (if short
			(list sentence)
			(append atomics (complex-sentences-in sentence)))))
    (make-truth-table :atomics atomics
		      :sentences sentences
		      :rows (compute-truth-entries atomics sentences))))

(defun print-truth-table (table &optional (stream t))
  "Print a truth table."
  (let* ((headers (mapcar #'sentence-output-form
			  (truth-table-sentences table)))
	 (width (+ (* 2 (length headers))
		   (sum headers #'length))))
    ;; Each sentence is printed as a column header, surrounded by 2 spaces
    (print-dashes width stream t)
    (format stream "~{ ~A ~}~%" headers)
    (print-dashes width stream t)
    (dolist (row (truth-table-rows table))
      (mapcar #'(lambda (entry header)
		  (print-centered (if entry "T" "F")
				  (+ 2 (length header))
				  stream))
	      row
	      headers)
      (format stream "~%"))
    (print-dashes width stream t)))

(defun compute-truth-entries (atomics sentences)
  "Compute the truth of each sentence under all interpretations of atomics."
  (mapcar #'(lambda (interpretation)
              (mapcar #'(lambda (sentence)
                          (interp sentence interpretation))
                sentences))
    (all-truth-interpretations atomics)))

(defun all-truth-interpretations (atomics)
  "Return all 2^n interpretations for a list of n atomics."
  (if (null atomics)
      (list nil)
    (let ((atomic (first atomics)))
      (mapcan #'(lambda (sub-rest)
                  `(((,atomic . t) . ,sub-rest)
                    ((,atomic . nil) . ,sub-rest)))
        (all-truth-interpretations (rest atomics))))))

(defun atomic-p (sentence)
  (or (eq sentence 't)
      (eq sentence 'nil)
      (atom sentence)
      (not (member (op sentence) '(or and not imply equiv)))))

(defun prop-atomics-in (sentence)
  "Return a list of all the propositional atomic sentences in <sentence>."
  (cond ((member sentence '(t nil)) nil)
        ((atom sentence) (list sentence))
        ((atomic-p sentence) (list sentence))
        (t (delete-duplicates (mapcan #'prop-atomics-in (args sentence))
                              :test #'equal
                              :from-end t))))

(defun complex-sentences-in (sentence)
  "Return a list of all non-atom sub-sentences of sentence."
  (cond ((atomic-p sentence) nil)
	(t (delete-duplicates
	    (nconc (mapcan #'complex-sentences-in (args sentence))
            (list sentence))))))

(defun sentence-output-form (sentence)
  "Convert a prefix sentence back into an infix notation with brief operators."
  (format nil "~{~A~^ ~}"
    (mklist (sublis '((and . "È") (not . "?") (or . "É") (equiv . "Ì"))
                    (prefix->infix sentence)))))

