using System;
using System.Collections;
using System.Collections.Generic;
using Accord;
using Accord.MachineLearning;
using Accord.MachineLearning.Boosting;

namespace MyIA.Trading.Backtester

{


    [Serializable]
    public class MultiClassBoost : MultiClassBoost<IClassifier<double[], int>, Weighted<IClassifier<double[], int>>,
        double[]>
    {
        public MultiClassBoost(IList<double> weights, IList<IClassifier<double[], int>> models) : base(weights, models)
        {

        }
    }


    /// <summary>Boosted classification model.</summary>
    /// <typeparam name="TModel">The type of the weak classifier.</typeparam>
    /// <typeparam name="TWeighted">The type of the weighted classifier.</typeparam>
    /// <typeparam name="TInput">The type of the input vectors accepted by the classifier.</typeparam>
    [Serializable]
    public class MultiClassBoost<TModel, TWeighted, TInput> : MulticlassClassifierBase<TInput>, IEnumerable<TWeighted>, IEnumerable where TModel : IClassifier<TInput, int> where TWeighted : Weighted<TModel, TInput>, new()
    {
        /// <summary>
        ///   Gets the list of weighted weak models
        ///   contained in this boosted classifier.
        /// </summary>
        public List<TWeighted> Models { get; private set; }

        /// <summary>
        ///   Initializes a new instance of the <see cref="T:Accord.MachineLearning.Boosting.Boost`1" /> class.
        /// </summary>
        public MultiClassBoost()
        {
            this.Models = new List<TWeighted>();
        }

        /// <summary>
        ///   Initializes a new instance of the <see cref="T:Accord.MachineLearning.Boosting.Boost`1" /> class.
        /// </summary>
        /// <param name="weights">The initial boosting weights.</param>
        /// <param name="models">The initial weak classifiers.</param>
        public MultiClassBoost(IList<double> weights, IList<TModel> models)
        {
            this.Models = new List<TWeighted>();
            if (weights.Count != models.Count)
                throw new DimensionMismatchException(nameof(models), "The number of models and weights must match.");
            for (int index = 0; index < weights.Count; ++index)
            {
                List<TWeighted> models1 = this.Models;
                TWeighted instance = Activator.CreateInstance<TWeighted>();
                instance.Weight = weights[index];
                instance.Model = models[index];
                models1.Add(instance);
            }
        }

        /// <summary>
        /// Computes a class-label decision for a given <paramref name="input" />.
        /// </summary>
        /// <param name="input">The input vector that should be classified into
        /// one of the <see cref="P:Accord.MachineLearning.ITransform.NumberOfOutputs" /> possible classes.</param>
        /// <returns>A class-label that best described <paramref name="input" /> according
        /// to this classifier.</returns>
        public override int Decide(TInput input)
        {
            var scores = new Dictionary<int, double>();
            foreach (TWeighted model in this.Models)
            {
                var classified = model.Model.Decide(input);
                if (!scores.ContainsKey(classified))
                {
                    scores[classified] = 0;
                }
                scores[classified] += model.Weight;

            }


            double score1, score0, score2;
            scores.TryGetValue(0, out score0);
            scores.TryGetValue(1, out score1);
            scores.TryGetValue(2, out score2);
            if (score1-score2>1)
            {
                return 1;
            }
            if (score2 - score1 > 1)
            {
                return 2;
            }

            return 0;
        }

        /// <summary>
        /// Computes a class-label decision for a given <paramref name="input" />.
        /// </summary>
        /// <param name="input">The input vector that should be classified into
        /// one of the <see cref="P:Accord.MachineLearning.ITransform.NumberOfOutputs" /> possible classes.</param>
        /// <returns>A class-label that best described <paramref name="input" /> according
        /// to this classifier.</returns>
        public List<int> DecideDetail(TInput input)
        {
            var scores = new List<int>(Models.Count);
            for (var index = 0; index < this.Models.Count; index++)
            {
                TWeighted model = this.Models[index];
                var classified = model.Model.Decide(input);
                scores.Add(classified) ;
            }


            return scores;
        }





        /// <summary>
        ///   Adds a new weak classifier and its corresponding
        ///   weight to the end of this boosted classifier.
        /// </summary>
        /// <param name="weight">The weight of the weak classifier.</param>
        /// <param name="model">The weak classifier</param>
        public void Add(double weight, TModel model)
        {
            List<TWeighted> models = this.Models;
            TWeighted instance = Activator.CreateInstance<TWeighted>();
            instance.Weight = weight;
            instance.Model = model;
            models.Add(instance);
        }

        /// <summary>
        ///   Gets or sets the <see cref="T:Accord.MachineLearning.Boosting.Weighted`1" /> at the specified index.
        /// </summary>
        public TWeighted this[int index]
        {
            get
            {
                return this.Models[index];
            }
            set
            {
                this.Models[index] = value;
            }
        }

        /// <summary>
        ///   Returns an enumerator that iterates through this collection.
        /// </summary>
        /// <returns>
        ///   An <see cref="T:System.Collections.IEnumerator" /> object that can be used to iterate through the collection.
        /// </returns>
        public IEnumerator<TWeighted> GetEnumerator()
        {
            return (IEnumerator<TWeighted>)this.Models.GetEnumerator();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return (IEnumerator)this.Models.GetEnumerator();
        }
    }
}