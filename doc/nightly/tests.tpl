% from bottle import template
% include('header.tpl')
% include('ijumbo.tpl')
% include('github.tpl')
% include('navbar.tpl')

    <div class="container">
      <div class="col-xs-8" role="main">
	
      	<table class="table table-striped table-condensed table-hover">
	  <thead><tr>
	      <th><code>{{filename}}</code></th>
	      <th><button type="button" class="btn btn-block btn-xs btn-primary">
		  Platform</button></th>
	      <th><button type="button" class="btn btn-block btn-xs btn-primary">
		  Test</button></th>
	      <th><button type="button" class="btn btn-block btn-xs btn-primary">
		  Result</button></th>
	  </tr></thead>

	  <tbody>
	    % for res in testres:
	    %  testcode=res['resultcode']
	    <tr>
	      <td></td>
	      <td>{{res['platform']}}</td>
	      <td>{{res['test']}}</td>
	      <td><a href="{{res['url']}}">
		% if testcode == 0:
		  <button class="btn btn-block btn-xs btn-success">
		% elif testcode == 1:
		  <button class="btn btn-block btn-xs btn-info">
		% elif testcode == 2:
		  <button class="btn btn-block btn-xs btn-warning">
		% elif testcode == 3:
		  <button class="btn btn-block btn-xs btn-danger">
		% end
		{{res['result']}}</button>
	      </a></td>
	    </tr>
	    % end
	  </tbody>
	</table>
      </div>
    </div>

% include('footer.tpl')
