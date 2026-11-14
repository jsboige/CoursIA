using System;
using System.Collections.Generic;

namespace MyIA.Trading.Backtester
{
    public class CompareBackTestings : IEqualityComparer<BackTestingSettings>
    {
        public bool Equals(BackTestingSettings item1, BackTestingSettings item2)
        {
            if (item1 == null && item2 == null)
                return true;
            else if ((item1 != null && item2 == null) ||
                     (item1 == null && item2 != null))
                return false;

            return String.Equals(item1.TrainingConfig.GetModelName(), item2.TrainingConfig.GetModelName(), StringComparison.Ordinal);
        }

        public int GetHashCode(BackTestingSettings item)
        {
            return item.TrainingConfig.GetModelName().GetHashCode();
        }
    }
}