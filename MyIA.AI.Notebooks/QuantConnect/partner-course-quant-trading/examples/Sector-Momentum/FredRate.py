# region imports
from AlgorithmImports import *
# endregion

class FredRate(PythonData):
    def GetSource(self, config, date, isLiveMode):
        return SubscriptionDataSource("https://fred.stlouisfed.org/graph/fredgraph.csv?id=DFF", SubscriptionTransportMedium.RemoteFile)

    def Reader(self, config, line, date, isLiveMode):
        data = line.split(',')
        if data[0] == 'DATE':
            return None
        rate = FredRate()
        rate.Symbol = config.Symbol
        rate.Time = datetime.strptime(data[0], "%Y-%m-%d")
        rate.Value = float(data[1])
        return rate
